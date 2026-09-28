# Lean seminar

## What this is

This is the shared Lean project of a 14-week seminar on Lean 4 and Mathlib, for
graduate students and anyone else who wants to learn. Lean is a language for
writing proofs that a computer checks, and Mathlib is its library of
mathematics. We meet for one hour a week. Most of the work happens at home, in
the exercise files here. Each participant also formalizes a problem from a
qualifying exam, that is, states and proves it in Lean, adds it to this
repository, and presents it in week 13 or 14.
The seminar's web page, with the schedule and each week's work, is
<https://oblomkov-math.github.io/LeanSeminar.html>.

## Getting started

You need about 10 GB of free disk space. 16 GB of memory is comfortable; 8 GB
works, but slowly.

1. **Install Lean and VS Code** by following <https://lean-lang.org/install/>.

   Or work in your browser instead, with nothing to install: this button opens
   the repository in GitHub Codespaces, a copy of VS Code that runs on GitHub
   with Lean and Mathlib set up for you.

   [![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/oblomkov-math/lean-seminar)

   The first start takes several minutes. Each GitHub account gets a limited
   number of free hours a month. In a codespace, skip steps 2–5. When you first
   save your work to GitHub, VS Code offers to make your fork (step 2) for you.

2. **Fork this repository**: press **Fork** at the top of this page. A fork is
   your own copy of the repository on GitHub, where you can save your work.

3. **Clone your fork**, which copies it to your computer:

   ```bash
   git clone https://github.com/<your-username>/lean-seminar.git
   cd lean-seminar
   ```

4. **Download the compiled Mathlib**, inside the `lean-seminar` folder:

   ```bash
   lake exe cache get
   ```

   This downloads several GB. Do not skip it: without it, Lean compiles all of
   Mathlib on your computer, which takes hours.

5. **Open the folder in VS Code**: **File → Open Folder…**, then choose the
   `lean-seminar` folder. Open the whole folder, not a single file; otherwise
   Lean cannot find Mathlib.

6. **Start with `Exercises/Week00_Squeeze.lean`.** The first time you open a
   file, Lean needs a minute or two to load Mathlib.

## Getting each week's new exercises

New exercise files appear here during the semester. To copy them into your own
copy, first tell git where this repository is. Do this once, in your
`lean-seminar` folder:

```bash
git remote add upstream https://github.com/oblomkov-math/lean-seminar.git
git config pull.rebase false
```

The first line gives this repository the name `upstream`; your fork is called
`origin`. (If git answers that `upstream` already exists, it is already set up.)
The second line tells git to combine the new files with your own work.

Then, each week, save your own work with a commit, and pull in the new files:

```bash
git add -A
git commit -m "My work"
git pull upstream main
```

If git opens an editor to ask for a message, save and close it.

## Layout

| Path | What is there |
|---|---|
| `Exercises/` | the weekly exercises, starting with `Week00_Squeeze.lean` |
| `Seminar/Diagnostics.lean` | the week 6 lab: junk values, vacuous theorems, `#print axioms` |
| `Seminar/ProjectTemplate.lean` | the template for your project |
| `Projects/` | the participants' projects, one folder each |
| `scripts/check.sh` | checks that a proof is really finished |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | fix the versions of Lean and Mathlib; don't change them |
| `.github/`, `.devcontainer/` | settings for GitHub's automatic build, the issue forms and Codespaces |

## Your project

[Projects/README.md](Projects/README.md) explains how to add your project to
this repository.

## Questions

Ask in [Discussions](https://github.com/oblomkov-math/lean-seminar/discussions),
this repository's question board. No question is too small: if you are stuck,
others probably are too.

## Mathlib is fixed for the semester

Everyone uses the same version of Mathlib all semester, so that everyone's files
work together. **Never run `lake update`.** It would move your copy to a newer
Mathlib, where lemma names differ, and your files would stop matching the
seminar's. If you ran it by accident, undo it with

```bash
git restore lake-manifest.json lean-toolchain
lake exe cache get
```
