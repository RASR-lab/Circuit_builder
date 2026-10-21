# Circuit Builder

A simple circuit and wiring editor for Windows, made for undergraduate labs.
Drag parts onto a grid, click pin-to-pin to wire them, and create your own parts with any pins you need.

![Circuit Builder](screenshot.png)

## Getting it running

**Option A: run it with Python (quickest)**

1. Install Python 3.8 or newer from <https://www.python.org/downloads/windows/>.
   In the installer, tick **"Add python.exe to PATH"**.
2. Double-click **`Run Circuit Builder.bat`**.

Nothing else needs installing; the app only uses Python's built-in Tkinter.
Optional: `pip install pillow` makes part pictures a little smoother and lets the app open WebP pictures too.

**Option B: make a stand-alone `.exe` (to share with a class)**

1. On any PC with Python installed, double-click **`Build Windows EXE.bat`**.
   It installs PyInstaller once and builds the app (takes about a minute).
2. Your app appears as **`dist\CircuitBuilder.exe`**. That single file runs on any Windows 10/11 PC without Python. Copy it to a USB stick or a shared drive.

Because the `.exe` is not code-signed, Windows SmartScreen may show "Windows protected your PC" the first time.
Click **More info → Run anyway**.

## How to use it

| To… | Do this |
|---|---|
| Add a part | Drag it from the **Components** list onto the grid, or double-click it and then click where it should go |
| Connect two pins | Click a pin (small circle), then click a pin on another part. You can also drag from pin to pin |
| Add corners to a wire | While wiring, click empty grid squares on the way. Backspace removes the last corner |
| Reshape a wire later | Double-click the wire to add a bend, then drag the white square |
| Edit label / value | Click the part and type in the panel on the right (e.g. `R1`, `4.7 kΩ`) |
| Give a part a picture | Click the part, then **Add picture…** in the panel on the right (see below) |
| Rotate / flip | **R** (Shift+R rotates the other way), **F** to flip |
| Delete | Select and press **Delete** (deleting a part also deletes its wires) |
| Copy, paste, duplicate | **Ctrl+C**, **Ctrl+V**, **Ctrl+D** |
| Undo / redo | **Ctrl+Z** / **Ctrl+Y** |
| Zoom / move around | Mouse wheel zooms; right- or middle-drag pans; **0** fits the circuit |
| Select several things | Drag a box around them, or Ctrl+click |

Pins show **filled** when connected and **hollow** while still free.
Hover over a pin to see its name and which net it is on.

**Ground and power rails:** every Ground symbol is connected together, and so is every Power Rail (VCC) with the same value (e.g. `+5 V`).
You can put a ground symbol wherever it's convenient instead of running long wires.

## Making your own components

Click **+ New Component** (top right), then:

1. **Details**: name, category, label prefix (`U` → U1, U2 …), optional default value, body color and picture.
2. **Pins**: type a pin name, pick the side it sticks out of (left, right, top or bottom) and press Enter.
   Type several names at once separated by commas, e.g. `VCC, GND, SDA, SCL`.
   Use **Move up/down** to reorder and **Add gap** to leave space between groups of pins.
   For chips, **Quick start: chip (DIP) with N pins** creates numbered pins 1…N in the standard order.
3. **Preview** updates as you go. Click **Save to library**.

Your parts appear under their category (marked ★) and are remembered for next time.
To start from an existing part (e.g. turn the Arduino Uno into a Mega), select it and click **Edit…**; built-in parts open as a copy.
If you change a part that's already in your circuit, the wires stay attached to pins with the same name.

## Pictures on parts

Any box-shaped part (your own parts, and built-in boards and modules like the Arduino Uno, servo or relay) can show a picture, such as a photo of the real module.
The picture sits in the middle of the part with the label underneath, and the pins stay where they are.

- **On the canvas:** click the part, then click **Add picture…** (or **Change picture…**) in the panel on the right and choose the file.
  The Component Editor opens with a preview; click **Save to library**.
  For a built-in part this saves your own copy (★) with the picture, and the part you clicked switches to it with its wires kept.
- **In the Component Editor:** use **Picture › Choose…** or click the empty picture box. **Remove** takes it off again.
- **In the parts list:** right-click a part and choose **Add picture…** (built-in parts: **Copy with a picture…**).

PNG, JPG, GIF and BMP pictures all work on Windows. Large photos are shrunk to 400 pixels when you add them, so files stay small.
With **Size → Automatic** ticked, the part grows to make room for the picture; untick it to set the size yourself.
Click the picture in the right-hand panel to see it bigger.
Schematic symbols (resistor, LED, logic gates …) keep their standard drawing. To make a picture version, select one in the list, click **Edit…** to make your own copy, and add the picture there.

Pictures are saved inside the part, so they travel with `.cblib` and `.circuit` files and appear in **Export image (SVG)**.

**Sharing parts:** *Components › Export my components* saves a `.cblib` file. Classmates load it with *Components › Import components*.
Circuit files also carry the custom parts they use, so opening someone's `.circuit` file adds their parts to your library automatically.
`examples\Sample components.cblib` has three ready-made modules to try.

## Checking your work

- **Connections** (toolbar) lists every *net*, a group of pins wired together that share the same voltage.
  Click a net to highlight it on the drawing. Export it as text, CSV (Excel), or a basic **SPICE** netlist for R, C, L, sources, diodes, LEDs and BJTs.
- **Check circuit** warns about shorted batteries and sources, parts that are shorted or not connected, free pins, and a missing ground.
  Double-click a message to jump to that part.
- **File › Export image (SVG)** saves a clean drawing for lab reports, pictures included. It opens in any browser, Word or PowerPoint.

## Built-in parts

Resistor, capacitor, electrolytic capacitor, inductor, potentiometer, LDR, fuse, battery, DC/AC voltage source, current source, power rail, ground, voltmeter, ammeter, switch, push button, lamp, DC motor, buzzer, diode, LED, NPN/PNP transistors, N-MOSFET, op-amp, AND/NAND/OR/NOR/XOR/NOT gates, Arduino Uno, 555 timer, 7805 regulator, generic 8- and 14-pin ICs, servo, ultrasonic sensor, TMP36, I2C LCD and relay module.

*File › Open example* has three ready-made circuits (also in the `examples` folder).

## Files and storage

- Circuits are saved as `.circuit` files (plain JSON, easy to grade or diff).
- Your component library and settings live in `%APPDATA%\CircuitBuilder\`.
  Copy `my_components.cblib` from there to back them up.
- To open a `.circuit` file by double-clicking, right-click it → *Open with* → choose `CircuitBuilder.exe`.

## For instructors: adding built-in parts

Every built-in part is one entry in the `BUILTIN_DEFS` list near the top of `circuit_builder.py`.
A chip or module is a single `BX(...)` line: id, name, category, label prefix, default value, description, width, height, and pins as `(name, side, position)`:

```python
BX("dht22", "DHT22 Sensor", "Modules & Sensors", "U", "", "Temperature & humidity sensor.",
   5, 4, [("VCC", "left", 1), ("DATA", "left", 2), ("GND", "left", 3)], color="#fef3c7"),
```

Rebuild the `.exe` afterwards if you hand that out.

## Troubleshooting

- **Nothing happens when I double-click the .bat**: Python isn't on the PATH. Reinstall Python and tick "Add python.exe to PATH".
- **Everything looks tiny or huge**: use the zoom buttons or **Fit**. The app follows your Windows display scaling.
- **I lost a custom part**: check `%APPDATA%\CircuitBuilder\my_components.cblib`, or re-import a `.cblib` / open a `.circuit` that used it.
