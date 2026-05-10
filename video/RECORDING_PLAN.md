# Recording Plan — ProofPulse Slides & Live Demo

This document describes a recommended, practical plan to record the slides and the live demo on Nobara (Fedora). It covers tools, settings, suggested takes/segments, and quick commands.

## Goals
- Produce a clear slide-driven video with synced audio.
- Record the live demo segments separately (terminal / VSCode) for easier editing.
- Keep recordings segmented so re-takes are minimal and editing is simple.

---

## Tools (install on Nobara/Fedora)
- OBS Studio — main recorder (screens, windows, webcam, mic). Install: `sudo dnf install obs-studio`
- ffmpeg — quick trims, format conversions: `sudo dnf install ffmpeg`
- pavucontrol — audio routing (PulseAudio/PipeWire GUI): `sudo dnf install pavucontrol`
- Kdenlive or Shotcut — video editor to assemble takes: `sudo dnf install kdenlive`
- (Optional) asciinema — terminal recording to replay/convert: `sudo dnf install asciinema`

Notes: Nobara uses PipeWire; OBS integrates with it. Use `pavucontrol` to make sure mic and system audio are set to the right sources.

---

## Recording Strategy / Takes
1. Setup & smoke test
   - Open `video/slides.html` in a Chromium/Firefox browser, press F11 for fullscreen.
   - Verify mic levels and do a 10–20s test recording in OBS.

2. Slides (primary recording)
   - Option A — Single-pass slides: record the entire slideshow in order (smooth, fewer cuts).
   - Option B — Per-slide segments: for fine control, record each slide as an individual take (start/stop OBS between slides).
   - Recommendation: Do a single-pass full run (Take A), then do per-slide quick re-takes for any problematic slides (Take B). This minimizes editing while keeping re-takes easy.

3. Slide transitions / special animations
   - Slide 2 has a two-phase reveal; record the transition slowly. If you need different narration for phase 1/2, record per-phase re-takes.

4. Live demo (separate capture)
   - Record the live demo separately from the slides. Use a separate OBS scene for VSCode + terminal captures.
   - Keep terminal font large and clear; use a dark theme with high contrast.
   - Record the demo in small segments (each demo step or example is its own take) so you can trim mistakes easily.

5. Voiceover & re-recorded audio
   - If live narration has issues, record a clean voiceover and replace slide audio in the editor.
   - Record voiceover after assembling the video (so you can pace to final timing).

6. Final full pass
   - After edits, do a final full-pass export (no narration mistakes, smooth transitions).

---

## OBS Recommended Settings (recording-focused)
- Output Mode: Advanced → Recording
  - Type: Standard
  - Recording Format: `mkv` (safer; remux to `mp4` later)
  - Encoder: `x264` or `NVENC` if GPU available
  - Rate Control: `CBR`
  - Bitrate: `12000` kbps (for 1080p) or `6000` for lower size
  - Keyframe Interval: 2
  - CPU Preset: `veryfast` (or `fast` if you have headroom)
- Video → Base (Canvas) Resolution: `1920x1080` (or match your display)
- Video → Output (Scaled) Resolution: `1920x1080`
- FPS: `30` (use `60` only for high-motion demos)
- Audio: 48 kHz, 16/24-bit; Mic bitrate 160 kbps

Remux MKV to MP4 after: `ffmpeg -i out.mkv -c copy out.mp4`

---

## Quick ffmpeg alternatives (if not using OBS):
- X11 (Xorg) screen capture:

```bash
ffmpeg -f x11grab -s 1920x1080 -r 30 -i :0.0 -f pulse -ac 2 -i default -c:v libx264 -preset veryfast -crf 18 -c:a aac out.mkv
```

- Wayland / PipeWire: prefer OBS or `wf-recorder`/`pipewire`-based capture tools; ffmpeg PipeWire capture is more advanced and OS-dependent.

---

## Microphone & Audio Tips
- Use a decent USB or XLR mic. Position 15–30 cm from mouth.
- Use `pavucontrol` to monitor levels; keep peaks around -6dB.
- Mute system sounds (notifications) during recordings.
- Consider monitoring with headphones to avoid feedback loops.

---

## Scene/Source Layout Suggestions (OBS)
- Scene A: Slides — Browser window capture (fullscreen) + mic
- Scene B: Demo — Window capture for VSCode + Window capture for terminal (side-by-side), mic, optionally webcam
- Scene C: Webcam full or picture-in-picture (optional)

Use OBS hotkeys to switch scenes between slides and demo.

---

## Filenames and Organization
- Use a clear convention: `YYYYMMDD_section_take_description.mkv`
  - Example: `20260508_slides_full_take1.mkv`
  - Example: `20260508_demo_terminal_loop1.mkv`
- Keep raw recordings in `video/raw/`, exports in `video/final/`, project files in `video/project/`.

---

## Editing Workflow (Kdenlive/Shotcut)
1. Import slide takes and demo takes into the timeline.
2. Trim start/end pauses. Snap clips so transitions are tight.
3. Add cross-fades or hard cuts per your style.
4. Replace audio with cleaned voiceover if available.
5. Add brief lower-third titles if needed (e.g., "Slide 3 — Three-Valued Coverage").
6. Export H.264 MP4 for upload: 1080p, 30fps, bitrate 8–12 Mbps.

Export example with ffmpeg (after edit):
```bash
ffmpeg -i project_export.mkv -c:v libx264 -preset slow -crf 20 -c:a aac -b:a 192k final.mp4
```

---

## Suggested Take Order (minimal re-takes)
1. Intro slide(s) — take whole run
2. Slide 2 (two-phase) — extra per-phase takes
3. Slide 3 (code-heavy) — one pass + 1 re-take if narration stumbles
4. Architecture slide — single pass
5. Evaluation/closing — single pass
6. Demo segments — record each demo step as a separate clip
7. Voiceover (if needed)
8. Final review pass

---

## Quick Checklist Before Recording
- [ ] Close notifications and set Do Not Disturb
- [ ] Set display scaling and font size for readability
- [ ] Confirm mic and desktop audio routing in `pavucontrol`
- [ ] Run a 10–20s test recording and review
- [ ] Ensure `video/raw/` directory exists

---

## Minimal Commands (install + test)
```bash
# Install main tools
sudo dnf install obs-studio ffmpeg kdenlive pavucontrol

# Simple ffmpeg test (Xorg)
ffmpeg -f x11grab -s 1280x720 -r 30 -i :0.0 -f pulse -i default -t 10 test.mkv
```

---

## Notes & Tips
- Record in segments for easier re-takes and smaller files.
- Use `mkv` during recording (safer); remux to `mp4` only after edits.
- Keep copies of all raw takes until the final video is published.


Good luck — I can also generate a short OBS scene collection/profile export or a minimal Kdenlive project template if you'd like. Let me know which extra files you'd like me to prepare.
