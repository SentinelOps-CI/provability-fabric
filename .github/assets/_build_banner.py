#!/usr/bin/env python3
"""Compose readme ASCII banner: Provability Fabric + verification spine visual."""
import pyfiglet
from pathlib import Path

WIDTH = 90

# Wordless verification spine:
#   · · ·           three pillars (prove / enforce / audit)
#   /|\|/|\         formal lattice converging on ⊢
#   ◇~~~ arch ~~~◇  fabric tension through runtime
#   ▓▓▓ band        sidecar membrane
#   <○─◆─○>         evidence convoy through checkpoint gate (◆)
#   ═══ rail        one shared track
SCENE = [
    "                      · · ·",
    "                     /|\\|/|\\",
    "                    / │ ⊢ │ \\",
    "                   /  │   │  \\",
    "              ◇~~~~~\\ │ /~~~~~◇",
    "             / ▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓ \\",
    "            <○───○───◆───○───○>",
    "           ══════════╪══════════",
]


def fig_lines(text: str, font: str = "small") -> list[str]:
    return pyfiglet.figlet_format(text, font=font).rstrip().splitlines()


def center(line: str, width: int = WIDTH) -> str:
    line = line[:width]
    pad = width - len(line)
    left = pad // 2
    return (" " * left + line + " " * (width - left - len(line)))[:width].ljust(width)


def center_block(lines: list[str], width: int = WIDTH) -> list[str]:
    block_w = max(len(ln) for ln in lines)
    if block_w > width:
        raise SystemExit(f"scene too wide ({block_w} > {width}): {lines!r}")
    left = (width - block_w) // 2
    return [((" " * left + ln).ljust(width))[:width] for ln in lines]


def frame(rows: list[str]) -> str:
    border = "#" * (WIDTH + 4)
    lines = [border, "# " + " " * WIDTH + " #"]
    for row in rows:
        lines.append("# " + row + " #")
    lines.append("# " + " " * WIDTH + " #")
    lines.append(border)
    return "\n".join(lines)


def main() -> None:
    title = [center(ln) for ln in fig_lines("Provability Fabric", font="small")]
    caption = center("--  Provability Fabric  --")
    scene = center_block(SCENE)
    spacer = center("")
    rows = title + [caption, spacer] + scene
    banner = frame(rows)

    for row in rows:
        if len(row) != WIDTH:
            raise SystemExit(f"width mismatch: {len(row)!r} {row!r}")

    out = Path(__file__).with_name("readme-banner.txt")
    out.write_text(banner + "\n", encoding="utf-8")
    print(banner)


if __name__ == "__main__":
    main()
