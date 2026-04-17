#!/usr/bin/env python3
"""Generate minimal Camera Synth PWA icons."""
import struct, zlib, os

def make_png(size, bg=(10,10,11), fg=(127,255,106)):
    """Generate a simple PNG icon with a waveform symbol."""
    w, h = size, size
    raw = []
    cx, cy = w // 2, h // 2
    r = int(w * 0.35)
    stroke = max(2, w // 48)

    for y in range(h):
        row = []
        for x in range(w):
            # Background
            pr, pg, pb = bg
            # Draw a simple oscilloscope-style sine wave
            nx = (x - cx) / r  # -1..1 roughly
            wave_y = cy + int(r * 0.4 * __import__('math').sin(nx * __import__('math').pi * 2))
            dist = abs(y - wave_y)
            # Outer circle
            circ = abs(((x-cx)**2 + (y-cy)**2)**0.5 - r)
            if circ < stroke:
                pr, pg, pb = fg
            elif dist < stroke and abs(nx) <= 1.0:
                pr, pg, pb = fg
            row += [pr, pg, pb, 255]
        raw.append(b'\x00' + bytes(row))

    def chunk(name, data):
        c = zlib.crc32(name + data) & 0xffffffff
        return struct.pack('>I', len(data)) + name + data + struct.pack('>I', c)

    sig = b'\x89PNG\r\n\x1a\n'
    ihdr_data = struct.pack('>IIBBBBB', w, h, 8, 2, 0, 0, 0)
    ihdr = chunk(b'IHDR', ihdr_data)
    idat = chunk(b'IDAT', zlib.compress(b''.join(raw), 9))
    iend = chunk(b'IEND', b'')
    return sig + ihdr + idat + iend

os.makedirs("icons", exist_ok=True)
for size in [192, 512]:
    png = make_png(size)
    with open(f"icons/icon-{size}.png", "wb") as f:
        f.write(png)
    print(f"Generated icons/icon-{size}.png ({len(png)} bytes)")

print("Done.")
