"""Regression tests for Circuit Builder.

Run from the project folder:

    python -m unittest discover -s tests -v

Only the Python standard library is needed.  The tests at the bottom open the real app window and
are skipped when there is no display (on Linux CI, run them under xvfb-run).
"""

import copy
import json
import math
import os
import random
import shutil
import sys
import tempfile
import time
import unittest

# Keep the tests away from the real component library and settings.
_TMP_HOME = tempfile.mkdtemp(prefix="cb_test_home_")
os.environ["APPDATA"] = _TMP_HOME
os.environ["HOME"] = _TMP_HOME
os.environ["USERPROFILE"] = _TMP_HOME

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

import circuit_builder as cb  # noqa: E402

EXAMPLES = ["led", "divider", "blink", "rc", "transistor", "blinker", "counter", "halfadder"]


def tearDownModule():
    shutil.rmtree(_TMP_HOME, ignore_errors=True)


def fresh_library():
    """An empty library in its own folder."""
    lib = cb.Library.__new__(cb.Library)
    lib.path = os.path.join(tempfile.mkdtemp(dir=_TMP_HOME), "my_components" + cb.LIB_EXT)
    lib.builtin = {d["id"]: d for d in cb.BUILTIN_DEFS}
    lib.custom, lib._cache, lib.problem = {}, {}, None
    return lib


class FakeApp:
    """Just enough of App for the simulator (no window needed)."""

    def __init__(self, data, library=None):
        self.library = library or fresh_library()
        for d in data.get("definitions", []):
            self.library.save_def(copy.deepcopy(d), persist=False)
        self.comps = {c["id"]: c for c in data["components"]}
        self.wires = {w["id"]: w for w in data["wires"]}

    def rdef(self, c):
        return self.library.resolve(c["def"])

    def compute_nets(self):
        return cb.compute_nets_of(self.comps, self.wires.values())


def comp_id(data, label):
    return next(c["id"] for c in data["components"] if c["label"] == label)


def run_for(sim, seconds, budget=20.0):
    """Advance the simulation by `seconds` of circuit time (real-time budget is generous)."""
    end = time.perf_counter() + budget
    while sim.t < seconds and not sim.error and time.perf_counter() < end:
        sim.advance(min(seconds - sim.t, 0.05) + 1e-12, budget=budget)
    return sim


# --------------------------------------------------------------------------- values & helpers
class ValueParsing(unittest.TestCase):
    def test_quantities(self):
        self.assertAlmostEqual(cb.qty("4.7 kΩ", "ohm"), 4700.0)
        self.assertAlmostEqual(cb.qty("100 nF", "f"), 100e-9)
        self.assertAlmostEqual(cb.qty("10 µF", "f"), 10e-6)
        self.assertAlmostEqual(cb.qty("2.2Meg", "ohm"), 2.2e6)
        self.assertAlmostEqual(cb.qty("10 V 60 Hz", "hz", allow_bare=False), 60.0)
        self.assertIsNone(cb.qty("hello", "v"))

    def test_fmt_si(self):
        self.assertEqual(cb.fmt_si(4.7e-3, "A"), "4.70 mA")
        self.assertEqual(cb.fmt_si(0, "V"), "0 V")
        self.assertEqual(cb.fmt_si(None, "V"), "—")
        self.assertEqual(cb.fmt_si(float("nan"), "V"), "—")

    def test_spice_value(self):
        self.assertEqual(cb.spice_value("4.7 kΩ"), "4.7k")
        self.assertEqual(cb.spice_value("1 MΩ"), "1Meg")
        self.assertEqual(cb.spice_value("10 µF"), "10u")


# --------------------------------------------------------------------------- chip logic
class Logic(unittest.TestCase):
    def test_half_adder_table(self):
        prog = cb.LogicProgram("SUM = A ^ B\nCARRY = A & B", ["A", "B", "SUM", "CARRY"])
        cols, rows = prog.truth_table()
        names = [c[0] for c in cols]
        for r in rows:
            v = dict(zip(names, r))
            self.assertEqual(v["SUM"], v["A"] ^ v["B"])
            self.assertEqual(v["CARRY"], v["A"] & v["B"])

    def test_precedence_and_not_forms(self):
        prog = cb.LogicProgram("Y = !A | B & C' ^ not D", ["A", "B", "C", "D", "Y"])
        for k in range(16):
            a, b, c, d = [(k >> i) & 1 for i in range(4)]
            s = [0] * len(prog.names)
            for n, v in zip("ABCD", (a, b, c, d)):
                s[prog.idx[n]] = v
            prog.settle(s)
            self.assertEqual(s[prog.idx["Y"]], (1 - a) | ((b & (1 - c)) ^ (1 - d)))

    def test_counter_counts(self):
        text = {t: x for t, _p, x in cb.LOGIC_TEMPLATES}["4-bit binary counter"]
        pins = ["CLK", "RST", "Q0", "Q1", "Q2", "Q3"]
        prog = cb.LogicProgram(text, pins)
        s, prev = [0] * len(prog.names), {}
        prog.step(s, prev)
        for n in range(1, 20):
            s[prog.idx["CLK"]] = 1
            prog.step(s, prev)
            s[prog.idx["CLK"]] = 0
            prog.step(s, prev)
            value = sum(s[prog.idx["Q%d" % i]] << i for i in range(4))
            self.assertEqual(value, n % 16)

    def test_errors_are_reported_not_raised(self):
        bad = ["Y = A & Q", "Y = A B", "Y = (A", "X = Y\nY = X", "Y = 2", "", "VCC = A"]
        for text in bad:
            res = cb.logic_program(text, ["A", "B", "Y", "VCC"])
            self.assertIsInstance(res, cb.LogicError, text)

    def test_deep_nesting_is_an_error(self):
        text = "Y = " + "(" * 400 + "A" + ")" * 400
        self.assertIsInstance(cb.logic_program(text, ["A", "Y"]), cb.LogicError)
        text = "Y = " + "!" * 3000 + "A"
        self.assertIsInstance(cb.logic_program(text, ["A", "Y"]), cb.LogicError)


# --------------------------------------------------------------------------- nets
class Nets(unittest.TestCase):
    def test_grounds_and_rails_join(self):
        comps = {
            "g1": {"id": "g1", "def": "ground"}, "g2": {"id": "g2", "def": "ground"},
            "r1": {"id": "r1", "def": "resistor"}, "r2": {"id": "r2", "def": "resistor"},
            "v1": {"id": "v1", "def": "vcc", "value": "5 V"}, "v2": {"id": "v2", "def": "vcc", "value": "+5V"},
        }
        wires = [{"id": "a", "a": ["r1", 0], "b": ["g1", 0]}, {"id": "b", "a": ["r2", 0], "b": ["g2", 0]},
                 {"id": "c", "a": ["r1", 1], "b": ["v1", 0]}, {"id": "d", "a": ["r2", 1], "b": ["v2", 0]},
                 {"id": "e", "a": ["gone", 0], "b": ["r1", 0]}]
        nets = cb.compute_nets_of(comps, wires)
        by_name = {n["name"]: n for n in nets}
        self.assertEqual(set(by_name["GND"]["pins"]), {("r1", 0), ("g1", 0), ("r2", 0), ("g2", 0)})
        self.assertEqual(set(by_name["GND"]["wires"]), {"a", "b"})
        rail = next(n for n in nets if ("v1", 0) in n["pins"])
        self.assertEqual(set(rail["pins"]), {("r1", 1), ("v1", 0), ("r2", 1), ("v2", 0)})
        self.assertNotIn("e", [w for n in nets for w in n["wires"]])


# --------------------------------------------------------------------------- reading damaged data
class Cleaning(unittest.TestCase):
    JUNK = [None, True, 0, -1, 1.5, float("nan"), float("inf"), "", "x", "abc", [], {}, [1], ["a"],
            ["a", "b"], ["a", 1, 2], {"x": 1}, [[1, 2]], [None, None], "#zzz", "#fff", 10 ** 30]

    def test_clean_functions_never_raise(self):
        rnd = random.Random(1)
        keys_c = ["id", "def", "x", "y", "rot", "flip", "label", "value", "notes", "wiper", "closed", "mcu"]
        keys_d = ["id", "pins", "symbol", "w", "h", "color", "image", "subcircuit", "pivot", "label_pt", "logic"]
        for _ in range(3000):
            c = {k: rnd.choice(self.JUNK) for k in keys_c if rnd.random() < 0.7}
            cc = cb.clean_comp(c)
            if cc is not None:
                self.assertIsInstance(cc["x"], (int, float))
                self.assertIn(cc["rot"], (0, 1, 2, 3))
                json.dumps(cc)
            w = {k: rnd.choice(self.JUNK) for k in ("id", "a", "b", "bends", "color") if rnd.random() < 0.8}
            cw = cb.clean_wire(w, lambda cid: 3)
            if cw is not None:
                self.assertTrue(0 <= cw["a"][1] < 3 and 0 <= cw["b"][1] < 3)
            d = {k: rnd.choice(self.JUNK) for k in keys_d if rnd.random() < 0.7}
            d["pins"] = [rnd.choice(self.JUNK + [{"name": "A", "side": rnd.choice(self.JUNK + ["top"]),
                                                  "pos": rnd.choice(self.JUNK)}]) for _ in range(rnd.randint(0, 4))]
            cd = cb.clean_def(d)
            if cd is not None:
                rd = cb.RDef(cd)   # must be drawable
                self.assertEqual(len(rd.pins), len(d["pins"]))
            cb.clean_settings(rnd.choice(self.JUNK + [{"recent": rnd.choice(self.JUNK), "wire_color": "red"}]))

    def test_def_pins_are_repaired_in_place(self):
        d = {"id": "custom_x", "name": "X", "pins": [{"name": "A", "side": "left", "pos": "abc"}, "junk",
                                                      {"name": "C", "side": "sideways", "pos": 3}]}
        cd = cb.clean_def(d)
        self.assertEqual([p["name"] for p in cd["pins"]], ["A", "2", "C"])
        self.assertEqual(cd["pins"][2]["side"], "left")
        cb.RDef(cd)

    def test_settings(self):
        self.assertEqual(cb.clean_settings([1, 2]), {})
        s = cb.clean_settings({"wire_style": "zigzag", "recent": ["a", 3, None], "theme": "dark"})
        self.assertNotIn("wire_style", s)
        self.assertEqual(s["recent"], ["a"])
        self.assertEqual(s["theme"], "dark")


class LibraryFile(unittest.TestCase):
    def _library_from(self, text):
        folder = os.path.join(_TMP_HOME, "CircuitBuilder")
        if os.path.isdir(folder):
            shutil.rmtree(folder)
        lib_home = os.path.join(_TMP_HOME, ".circuit_builder")
        if os.path.isdir(lib_home):
            shutil.rmtree(lib_home)
        path = os.path.join(cb.data_dir(), "my_components" + cb.LIB_EXT)
        with open(path, "w", encoding="utf-8") as f:
            f.write(text)
        return cb.Library(), path

    def test_damaged_library_is_backed_up_not_lost(self):
        lib, path = self._library_from('{"components": [{"id": "custom_a", "name": "A", "pins": [')
        self.assertIsNotNone(lib.problem)
        backups = [f for f in os.listdir(os.path.dirname(path)) if ".damaged-" in f]
        self.assertEqual(len(backups), 1)
        with open(os.path.join(os.path.dirname(path), backups[0]), encoding="utf-8") as f:
            self.assertIn("custom_a", f.read())

    def test_good_entries_survive_bad_ones(self):
        good = {"id": "custom_g", "name": "G", "symbol": "box", "pins": [{"name": "A", "side": "left", "pos": 1}]}
        text = json.dumps({"components": [good, "junk", {"id": "resistor", "pins": []}]})
        lib, _path = self._library_from(text)
        self.assertIn("custom_g", lib.custom)
        self.assertNotIn("resistor", lib.custom)       # can't shadow a built-in part
        self.assertIn("could not be loaded", lib.problem)

    def test_bom_is_accepted(self):
        good = {"id": "custom_b", "name": "B", "pins": [{"name": "A", "side": "left", "pos": 1}]}
        lib, _path = self._library_from("﻿" + json.dumps({"components": [good]}))
        self.assertIn("custom_b", lib.custom)
        self.assertIsNone(lib.problem)


class NestedComponents(unittest.TestCase):
    def test_pin_reorder_reaches_components_built_from_circuits(self):
        lib = fresh_library()
        part = {"id": "custom_p", "name": "P", "symbol": "box", "w": 4, "h": 3,
                "pins": [{"name": "A", "side": "left", "pos": 1}, {"name": "B", "side": "right", "pos": 1},
                         {"name": "C", "side": "right", "pos": 2}]}
        lib.save_def(copy.deepcopy(part), persist=False)
        outer = {"id": "custom_q", "name": "Q", "symbol": "box", "w": 4, "h": 3,
                 "pins": [{"name": "IN", "side": "left", "pos": 1, "inner": ["p1", 1]},
                          {"name": "X", "side": "right", "pos": 1, "inner": ["p1", 2]}],
                 "subcircuit": {"comps": [{"id": "p1", "def": "custom_p", "x": 0, "y": 0},
                                          {"id": "r1", "def": "resistor", "x": 6, "y": 0}],
                                "wires": [{"id": "w1", "a": ["p1", 1], "b": ["r1", 0]},
                                          {"id": "w2", "a": ["p1", 2], "b": ["r1", 1]}]}}
        lib.save_def(copy.deepcopy(outer), persist=False)
        # P's pins become B, A (C deleted): inner wire on B moves to pin 0, the one on C goes
        old_names = ["A", "B", "C"]
        new = dict(part, pins=[{"name": "B", "side": "left", "pos": 1}, {"name": "A", "side": "left", "pos": 2}])
        lib.save_def(new, persist=False)
        mapping = cb.App._pin_mapping(old_names, lib.resolve("custom_p").pins)
        dropped = lib.remap_nested("custom_p", mapping)
        q = lib.get("custom_q")
        self.assertEqual(dropped, 1)
        self.assertEqual([w["a"] for w in q["subcircuit"]["wires"]], [["p1", 0]])
        self.assertEqual(q["pins"][0]["inner"], ["p1", 0])
        self.assertNotIn("inner", q["pins"][1])


# --------------------------------------------------------------------------- simulator
class Simulation(unittest.TestCase):
    def test_every_example_simulates(self):
        for name in EXAMPLES:
            with self.subTest(example=name):
                sim = run_for(cb.Sim(FakeApp(cb.build_example(name))), 0.05)
                self.assertIsNone(sim.error, name)

    def test_divider_reads_half(self):
        data = cb.build_example("divider")
        sim = run_for(cb.Sim(FakeApp(data)), 0.01)
        vm = sim.by_cid[comp_id(data, "VM1")]
        # 10 MΩ voltmeter across a 5 kΩ source: 5 V × 10M / (10M + 5k)
        self.assertAlmostEqual(vm.vd(sim.x), 5.0 * 10e6 / (10e6 + 5e3), places=4)

    def test_led_current(self):
        data = cb.build_example("led")
        sim = run_for(cb.Sim(FakeApp(data)), 0.01)
        i = sim.by_cid[comp_id(data, "D1")].currents(sim.x)[0]
        self.assertTrue(0.010 < i < 0.020, i)

    def test_rc_cutoff(self):
        data = cb.build_example("rc")
        app = FakeApp(data)
        sim = cb.Sim(app)
        src = sim.by_cid[comp_id(data, "V1")]
        out = sim.node_of[(comp_id(data, "Vout"), 0)]
        fc = 1 / (2 * math.pi * 1e3 * 100e-9)
        h = sim.ac_sweep(src, out, [fc / 100, fc, fc * 100])
        db = [20 * math.log10(abs(v)) for v in h]
        self.assertAlmostEqual(db[0], 0.0, delta=0.05)
        self.assertAlmostEqual(db[1], -3.01, delta=0.1)
        self.assertAlmostEqual(db[2], -40.0, delta=0.5)

    def test_flip_flop_counter_steps(self):
        data = cb.build_example("counter")
        sim = run_for(cb.Sim(FakeApp(data)), 3.2)
        self.assertIsNone(sim.error)
        edges = [d.edges for d in sim.devs if isinstance(d, cb.FlipFlop)]
        self.assertTrue(edges and max(edges) >= 2, edges)

    def test_logic_chip_in_simulator(self):
        # a 74HC08 AND gate powered from 5 V, inputs tied high and low
        comps = [{"id": "u", "def": "74hc08", "x": 0, "y": 0, "label": "U1", "value": ""},
                 {"id": "p", "def": "vcc", "x": 0, "y": -5, "label": "VCC", "value": "5 V"},
                 {"id": "g", "def": "ground", "x": 0, "y": 9, "label": "GND", "value": ""}]
        if not any(d["id"] == "74hc08" for d in cb.BUILTIN_DEFS):
            self.skipTest("no 74hc08 part")
        names = [p["name"] for p in cb.RDef(next(d for d in cb.BUILTIN_DEFS if d["id"] == "74hc08")).pins]
        pin = names.index
        wires = [{"id": "1", "a": ["u", pin("VCC")], "b": ["p", 0]}, {"id": "2", "a": ["u", pin("GND")], "b": ["g", 0]},
                 {"id": "3", "a": ["u", pin("1A")], "b": ["p", 0]}, {"id": "4", "a": ["u", pin("1B")], "b": ["p", 0]},
                 {"id": "5", "a": ["u", pin("2A")], "b": ["p", 0]}, {"id": "6", "a": ["u", pin("2B")], "b": ["g", 0]}]
        sim = run_for(cb.Sim(FakeApp({"components": comps, "wires": wires})), 0.01)
        self.assertIsNone(sim.error)
        self.assertGreater(sim.pin_v(("u", pin("1Y"))), 4.5)
        self.assertLess(sim.pin_v(("u", pin("2Y"))), 0.5)

    def test_bad_pin_wire_does_not_break_simulator(self):
        data = cb.build_example("led")
        data["wires"].append({"id": "bad", "a": [comp_id(data, "R1"), 9], "b": [comp_id(data, "D1"), 0]})
        sim = run_for(cb.Sim(FakeApp(data)), 0.01)
        self.assertIsNone(sim.error)


class BuiltinParts(unittest.TestCase):
    def test_every_builtin_part_resolves(self):
        ids = set()
        for d in cb.BUILTIN_DEFS:
            self.assertNotIn(d["id"], ids, "duplicate id")
            ids.add(d["id"])
            rd = cb.RDef(d)
            self.assertTrue(rd.pins, d["id"])
            if d.get("logic"):
                self.assertNotIsInstance(cb.logic_program(d["logic"], [p["name"] for p in rd.pins]),
                                         cb.LogicError, d["id"])

    def test_example_files_load(self):
        folder = os.path.join(ROOT, "examples")
        for f in sorted(os.listdir(folder)):
            path = os.path.join(folder, f)
            data = cb.load_json(path, None)
            self.assertIsInstance(data, dict, f)
            if f.endswith(cb.FILE_EXT):
                n = len(data["components"])
                self.assertEqual(len([c for c in map(cb.clean_comp, data["components"]) if c]), n, f)
                for d in data.get("definitions", []):
                    self.assertIsNotNone(cb.clean_def(d), f)
            elif f.endswith(cb.LIB_EXT):
                for d in data["components"]:
                    self.assertIsNotNone(cb.clean_def(d), f)


# --------------------------------------------------------------------------- symbol styles
class SymbolStyles(unittest.TestCase):
    def tearDown(self):
        cb.set_symbol_style("ansi")

    def test_iec_symbols_keep_every_pin(self):
        """Switching to IEC symbols must never move a pin (wires stay attached)."""
        for d in cb.BUILTIN_DEFS:
            cb.set_symbol_style("ansi")
            a = cb.RDef(d)
            cb.set_symbol_style("iec")
            b = cb.RDef(d)
            self.assertEqual(a.pins, b.pins, d["id"])
            self.assertEqual(a.pivot, b.pivot, d["id"])
            if d.get("symbol") in cb.IEC_SYMBOLS:
                self.assertNotEqual(a.prims, b.prims, d["id"])
                # the drawing stays near its pins
                x0, y0, x1, y1 = b.body_bbox
                px = [p["x"] for p in b.pins]
                py = [p["y"] for p in b.pins]
                self.assertTrue(x0 >= min(px) - 1.5 and x1 <= max(px) + 2.5, d["id"])
                self.assertTrue(y0 >= min(py) - 1.5 and y1 <= max(py) + 1.5, d["id"])

    def test_iec_resistor_is_a_box(self):
        cb.set_symbol_style("iec")
        rd = cb.RDef(next(d for d in cb.BUILTIN_DEFS if d["id"] == "resistor"))
        self.assertTrue(any(p["t"] == "poly" and len(p["pts"]) == 4 for p in rd.prims))
        cb.set_symbol_style("nonsense")
        self.assertEqual(cb.SYMBOL_STYLE["style"], "ansi")

    def test_style_setting_is_checked(self):
        self.assertEqual(cb.clean_settings({"symbol_style": "iec"})["symbol_style"], "iec")
        self.assertNotIn("symbol_style", cb.clean_settings({"symbol_style": "din"}))


# --------------------------------------------------------------------------- SPICE and KiCad export
def _builder():
    """Tiny circuit builder for export tests: add(def, label, value) -> id; w(a, pin, b, pin)."""
    comps, wires = [], []

    def add(did, label, value=None, **kw):
        d = next(b for b in cb.BUILTIN_DEFS if b["id"] == did)
        cid = "p%d" % (len(comps) + 1)
        c = {"id": cid, "def": did, "x": 5 * len(comps), "y": 0, "rot": 0, "flip": False, "label": label,
             "value": d["value"] if value is None else value}
        c.update(kw)
        comps.append(c)
        return cid

    def w(a, ap, b, bp):
        def idx(cid, name):
            c = next(c for c in comps if c["id"] == cid)
            rd = cb.RDef(next(b for b in cb.BUILTIN_DEFS if b["id"] == c["def"]))
            return next(i for i, p in enumerate(rd.pins) if p["name"] == name)
        wires.append({"id": "w%d" % (len(wires) + 1), "a": [a, idx(a, ap)], "b": [b, idx(b, bp)]})

    def data():
        return {"components": comps, "wires": wires, "definitions": []}
    return add, w, data


def _amp_circuit():
    """Non-inverting op-amp (gain 11) with a logic gate and a regulator: parts that need subcircuits."""
    add, w, data = _builder()
    vin = add("dc_source", "VIN", "0.5 V")
    g = add("ground", "GND1")
    w(vin, "−", g, "GND")
    u1 = add("opamp", "U1", "LM741")
    w(vin, "+", u1, "IN+")
    rf, rg = add("resistor", "RF", "10 kΩ"), add("resistor", "RG", "1 kΩ")
    w(u1, "OUT", rf, "1"); w(rf, "2", u1, "IN−"); w(rg, "1", u1, "IN−"); w(rg, "2", g, "GND")
    vp, vn = add("vcc", "PWR1", "+15 V"), add("vcc", "PWR2", "-15 V")
    w(u1, "V+", vp, "V"); w(u1, "V−", vn, "V")
    x = add("xor", "G1")
    p5 = add("vcc", "PWR3", "+5 V")
    w(x, "A", p5, "V"); w(x, "B", g, "GND")
    rx = add("resistor", "R3", "10 kΩ"); w(x, "Y", rx, "1"); w(rx, "2", g, "GND")
    bat = add("battery", "B1", "9 V"); w(bat, "−", g, "GND")
    reg = add("reg7805", "U2", ""); w(bat, "+", reg, "IN"); w(reg, "GND", g, "GND")
    rl = add("resistor", "RL", "100 Ω"); w(reg, "OUT", rl, "1"); w(rl, "2", g, "GND")
    return data()


class SpiceExport(unittest.TestCase):
    def test_spice_num(self):
        self.assertEqual(cb.spice_num(4700), "4.7k")
        self.assertEqual(cb.spice_num(1e6), "1Meg")
        self.assertEqual(cb.spice_num(100e-9), "100n")
        self.assertEqual(cb.spice_num(-15), "-15")
        self.assertEqual(cb.spice_num(0), "0")
        self.assertEqual(cb.spice_num(1e-18), "1e-18")

    def test_every_example_exports_in_every_analysis(self):
        for name in EXAMPLES:
            app = FakeApp(cb.build_example(name))
            for kind, directive in (("op", ".op"), ("tran", ".tran "), ("ac", ".ac dec ")):
                text, skipped = cb.spice_netlist(app, {"type": kind})
                lines = text.splitlines()
                self.assertTrue(lines[0].startswith("*"), name)   # SPICE's first line is the title
                self.assertEqual(lines[-1], ".end", name)
                self.assertTrue(any(l.startswith(directive) for l in lines), (name, kind))
                text.encode("ascii")   # plain ASCII for every SPICE
                for s in skipped:
                    self.assertIn(s, text)

    def test_values_match_the_simulator(self):
        text, skipped = cb.spice_netlist(FakeApp(_amp_circuit()), {"type": "op"})
        self.assertEqual(skipped, [])
        self.assertIn(".subckt CB_OPAMP inm inp out vp vn", text)
        self.assertIn(".subckt CB_XOR a b y", text)
        self.assertIn(".subckt CB_REG_5 in out gnd", text)
        self.assertIn("RF N2 N3 10k", text.replace("RF N3 N2", "RF N2 N3"))
        self.assertRegex(text, r"(?m)^V_B1 \S+ \S+ DC 9$")       # battery + internal resistance
        self.assertRegex(text, r"(?m)^R_B1_int \S+ 0 1\.5$")
        self.assertRegex(text, r"(?m)^V_PWR2 NEG15V 0 DC -15$")   # rails become sources

    def test_ac_input_and_unwired_op_amp_supplies(self):
        add, w, data = _builder()
        v = add("ac_source", "V1", "1 V 1 kHz")
        g = add("ground", "GND1")
        w(v, "2", g, "GND")
        u = add("opamp", "U1", "LM358")
        w(v, "1", u, "IN+"); w(u, "OUT", u, "IN−")
        text, _ = cb.spice_netlist(FakeApp(data()), {"type": "ac", "fstart": 10, "fstop": 1e5, "ppd": 5})
        self.assertRegex(text, r"(?m)^V1 \S+ 0 DC 0 AC 1 SIN\(0 1 1k\)$")
        self.assertIn(".ac dec 5 10 100k", text)
        self.assertRegex(text, r"(?m)^V_U1_VP U1_VP 0 DC 15$")      # ±15 V assumed, as in the simulator
        self.assertIn("CB_OPAMP_LM358", text)

    def test_circuit_that_cannot_simulate_is_refused(self):
        add, w, data = _builder()
        p = add("vcc", "PWR1", "+5 V")
        g = add("ground", "GND1")
        w(p, "V", g, "GND")
        with self.assertRaises(cb.SimError):
            cb.spice_netlist(FakeApp(data()))

    @unittest.skipUnless(shutil.which("ngspice"), "ngspice is not installed")
    def test_ngspice_agrees_with_the_simulator(self):
        import re
        import subprocess
        app = FakeApp(_amp_circuit())
        text, _ = cb.spice_netlist(app, {"type": "op"})
        text = text.replace(".end\n", ".control\nop\nprint all\n.endc\n.end\n")
        d = tempfile.mkdtemp(dir=_TMP_HOME)
        path = os.path.join(d, "amp.cir")
        with open(path, "w") as f:
            f.write(text)
        res = subprocess.run(["ngspice", "-b", path], capture_output=True, text=True, timeout=120).stdout
        vals = {m.group(1): float(m.group(2))
                for m in re.finditer(r"(?m)^\s*([\w.]+)\s*=\s*([-+0-9.eE]+)\s*$", res)}
        sim = cb.Sim(app)
        x = sim._dc(sim.S, [0.0] * sim.N)
        checked = 0
        for i in range(1, sim.nn + 1):
            nm = cb._spice_ident(sim.node_names[i]).lower()
            if nm in vals:
                self.assertAlmostEqual(vals[nm], x[i - 1], delta=0.01, msg=nm)
                checked += 1
        self.assertGreaterEqual(checked, 6)


class KicadExport(unittest.TestCase):
    def _parse(self, text):
        import re
        toks = re.findall(r'\(|\)|"(?:\\.|[^"\\])*"|[^\s()"]+', text)
        depth = 0
        for t in toks:
            depth += t == "("
            depth -= t == ")"
            self.assertGreaterEqual(depth, 0)
        self.assertEqual(depth, 0)
        return toks

    def test_pads_follow_the_real_parts(self):
        app = FakeApp(cb.build_example("transistor"))
        text, skipped = cb.kicad_netlist(app)
        self._parse(text)
        self.assertTrue(text.startswith('(export (version "E")'))
        # an NPN in TO-92 is E-B-C, and an LED's pad 1 is its cathode
        self.assertIn('(node (ref "Q1") (pin "2") (pinfunction "B"))', text)
        self.assertIn('(node (ref "D1") (pin "1") (pinfunction "K"))', text)
        self.assertIn('(footprint "Package_TO_SOT_THT:TO-92_Inline")', text)

    def test_simulation_parts_are_left_out(self):
        text, skipped = cb.kicad_netlist(FakeApp(cb.build_example("divider")))
        self.assertIn("V1", skipped)
        self.assertNotIn('(ref "V1")', text)
        self.assertNotIn('(ref "GND', text)

    def test_every_example_and_duplicate_labels(self):
        for name in EXAMPLES:
            self._parse(cb.kicad_netlist(FakeApp(cb.build_example(name)))[0])
        add, w, data = _builder()
        a, b = add("resistor", "R1"), add("resistor", "R1")
        w(a, "2", b, "1")
        text, _ = cb.kicad_netlist(FakeApp(data()))
        self.assertIn('(ref "R1")', text)
        self.assertIn('(ref "R2")', text)


# --------------------------------------------------------------------------- the real app (needs a display)
def _tk_root():
    try:
        import tkinter as tk
        root = tk.Tk()
        root.withdraw()
        return root
    except Exception:
        return None


class AppTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = _tk_root()
        if cls.root is None:
            raise unittest.SkipTest("no display for Tk")
        cls.messages = []
        for name in ("showerror", "showwarning", "showinfo"):
            setattr(cb.messagebox, name, lambda *a, _n=name, **k: cls.messages.append((_n, a[1] if len(a) > 1 else "")))
        cb.messagebox.askyesno = lambda *a, **k: True
        cb.messagebox.askyesnocancel = lambda *a, **k: False
        cls.root.geometry("1200x800")
        cls.app = cb.App(cls.root)
        cls.root.update()

    @classmethod
    def tearDownClass(cls):
        try:
            cls.app.sim_stop()
            cls.root.destroy()
        except Exception:
            pass

    def setUp(self):
        self.messages.clear()
        self.errors = []
        self.root.report_callback_exception = lambda *a: self.errors.append(a)
        self.app.dirty = False
        self.app.sim_stop()
        self.app.new_file()
        self.app.dirty = False

    def pump(self):
        for _ in range(3):
            self.root.update()

    def tearDown(self):
        self.pump()
        self.assertEqual(self.errors, [], "errors in Tk callbacks")

    def test_examples_open_and_draw(self):
        for name in EXAMPLES:
            self.app.dirty = False
            self.app.load_example(name)
            self.app._redraw()
        self.pump()

    def test_damaged_file_keeps_current_circuit(self):
        self.app.load_example("divider")
        before = copy.deepcopy(self.app.comps)
        bad = {"format": "circuit-builder", "components": ["junk", {"id": 3}], "wires": []}
        with self.assertRaises(ValueError):
            self.app.load_data(bad)
        self.assertEqual(self.app.comps, before)

    def test_file_with_bad_wires_opens_with_a_note(self):
        data = cb.build_example("led")
        data["wires"] += [{"id": "x1", "a": [comp_id(data, "R1"), 5], "b": [comp_id(data, "D1"), 0]},
                          {"id": "x2"}, "junk"]
        del data["components"][0]["x"]
        path = os.path.join(tempfile.mkdtemp(dir=_TMP_HOME), "bad.circuit")
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f)
        self.app.open_file(path)
        self.assertEqual(len(self.app.wires), 4)
        self.assertTrue(any("removed" in m for _n, m in self.messages))
        self.app._redraw()

    def test_missing_part_type_with_huge_pin_number(self):
        data = cb.build_example("led")
        data["components"].append({"id": "m1", "def": "custom_not_in_library", "x": 30, "y": 0, "label": "U9"})
        data["wires"] += [{"id": "m", "a": ["m1", 999999], "b": [comp_id(data, "R1"), 0]},
                          {"id": "ok", "a": ["m1", 3], "b": [comp_id(data, "R1"), 1]}]
        self.app.load_data(data)
        self.assertNotIn("m", self.app.wires)
        self.assertIn("ok", self.app.wires)
        self.assertEqual(len(self.app.rdef(self.app.comps["m1"]).pins), 4)   # placeholder sized from its wires
        self.app._redraw()

    def test_save_and_reopen_round_trip(self):
        self.app.load_example("halfadder")
        path = os.path.join(tempfile.mkdtemp(dir=_TMP_HOME), "rt.circuit")
        self.app.path = path
        self.assertTrue(self.app.save())
        comps, wires = copy.deepcopy(self.app.comps), copy.deepcopy(self.app.wires)
        self.app.open_file(path)
        self.assertEqual(self.app.comps, comps)
        self.assertEqual(self.app.wires, wires)

    def _custom_part(self, pins):
        return {"id": "custom_t", "name": "T", "category": "My Components", "prefix": "U", "value": "",
                "description": "", "symbol": "box", "w": 4, "h": 4, "color": "#e8eefc",
                "pins": [{"name": n, "side": "left", "pos": i + 1} for i, n in enumerate(pins)]}

    def test_undo_after_editing_a_part_type(self):
        app = self.app
        app.save_definition(self._custom_part(["A", "B", "C"]))
        cid = app.place_component("custom_t", 0, 0)
        rid = app.place_component("resistor", 8, 0)
        app.wiring = {"start": (cid, 2), "bends": []}
        app.finish_wire((rid, 0))
        self.assertEqual(len(app.wires), 1)
        app.save_definition(self._custom_part(["A", "B"]))     # pin C removed: its wire goes
        self.assertEqual(len(app.wires), 0)
        app.undo()                                              # the restored wire points at pin C
        self.assertEqual(len(app.wires), 0)
        app._redraw()

    def test_reordered_pins_in_an_old_file_keep_their_wires(self):
        app = self.app
        app.save_definition(self._custom_part(["A", "B"]))
        cid = app.place_component("custom_t", 0, 0)
        rid = app.place_component("resistor", 8, 0)
        app.wiring = {"start": (cid, 1), "bends": []}           # wire on B
        app.finish_wire((rid, 0))
        data = json.loads(json.dumps(app.serialize()))
        app.save_definition(self._custom_part(["B", "A"]))      # library copy changes after saving
        app.dirty = False
        app.load_data(data)
        w = next(iter(app.wires.values()))
        end = w["a"] if w["a"][0] == cid else w["b"]
        self.assertEqual(app.rdef(app.comps[cid]).pins[end[1]]["name"], "B")

    def test_simulation_loop_survives_an_error(self):
        app = self.app
        app.load_example("rc")
        app.sim_start()
        orig = app._sim_draw
        app._sim_draw = lambda: 1 / 0
        try:
            app._sim_tick()
        finally:
            app._sim_draw = orig
        self.assertIsNotNone(app._sim_job, "the loop stopped")
        self.assertIn("internal problem", app.sim.error)
        app.sim_stop()

    def test_callback_errors_are_logged(self):
        try:
            raise RuntimeError("test error 12345")
        except RuntimeError:
            self.app._on_tk_error(*sys.exc_info())
        with open(cb.error_log_path(), encoding="utf-8") as f:
            self.assertIn("test error 12345", f.read())

    def test_import_library_skips_junk(self):
        path = os.path.join(tempfile.mkdtemp(dir=_TMP_HOME), "lib.cblib")
        good = self._custom_part(["X", "Y"])
        good["id"] = "custom_imp"
        with open(path, "w", encoding="utf-8") as f:
            json.dump({"format": "circuit-builder-library", "components": [good, "junk", {"id": "x"}]}, f)
        orig = cb.filedialog.askopenfilename
        cb.filedialog.askopenfilename = lambda *a, **k: path
        try:
            self.app.import_library()
        finally:
            cb.filedialog.askopenfilename = orig
        self.assertIn("custom_imp", self.app.library.custom)
        self.assertTrue(any("could not be used" in m for _n, m in self.messages))

    def test_symbol_style_switch_redraws(self):
        self.app.load_example("halfadder")
        try:
            self.app.set_symbol_style("iec")
            self.app._redraw()
            self.pump()
            self.assertEqual(self.app.settings["symbol_style"], "iec")
            self.assertEqual(self.app.v_symbol_style.get(), "iec")
            rd = self.app.rdef(next(c for c in self.app.comps.values() if c["def"] == "xor"))
            self.assertTrue(any(p["t"] == "text" and p["s"] == "=1" for p in rd.prims))
        finally:
            self.app.set_symbol_style("ansi")

    def test_spice_dialog_previews_and_saves(self):
        self.app.load_example("rc")
        dlg = cb.SpiceDialog(self.app)
        self.pump()
        self.assertIn(".tran ", dlg.text)
        dlg.v_type.set("ac")
        dlg._show_fields()
        self.assertIn(".ac dec ", dlg.text)
        self.assertIn("AC 1", dlg.text)
        dlg.v_fstop.set("nonsense")
        dlg._refresh()
        self.assertIn("disabled", dlg.b_save.state())
        dlg.v_fstop.set("1 MHz")
        dlg._refresh()
        path = os.path.join(tempfile.mkdtemp(dir=_TMP_HOME), "rc.cir")
        orig = cb.filedialog.asksaveasfilename
        cb.filedialog.asksaveasfilename = lambda **k: path
        try:
            dlg._save()
        finally:
            cb.filedialog.asksaveasfilename = orig
        with open(path) as f:
            self.assertIn(".ac dec 20 ", f.read())

    def test_kicad_export_from_the_menu(self):
        self.app.load_example("transistor")
        path = os.path.join(tempfile.mkdtemp(dir=_TMP_HOME), "t.net")
        orig = cb.filedialog.asksaveasfilename
        cb.filedialog.asksaveasfilename = lambda **k: path
        try:
            self.app.export_kicad()
        finally:
            cb.filedialog.asksaveasfilename = orig
        with open(path, encoding="utf-8") as f:
            self.assertIn('(ref "Q1")', f.read())


if __name__ == "__main__":
    unittest.main()
