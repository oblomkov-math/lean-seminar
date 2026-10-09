# Projects

Each participant formalizes a problem from a qualifying exam, that is, states
and proves it in Lean, and adds it here in a folder of their own:
`Projects/<YourName>/`. You present yours in week 13 or 14.

`lake build` builds every `.lean` file in this folder, so you don't need to
list your files anywhere.

For a finished example, see [`Example/EvenMul.lean`](Example/EvenMul.lean):
the template filled in for an easy problem, that an even integer times any
integer is even.

## How to add your project

1. **Fork this repository, and start a branch for your project.** A fork is
   your own copy of the repository on GitHub: press **Fork** at the top of the
   repository's page, then clone your fork. If you already have a fork and a
   clone for the exercises, use those.

   A branch keeps your project apart from your exercise solutions, so that your
   pull request contains only the project. In your clone, run

   ```bash
   git fetch upstream
   git switch -c project upstream/main
   ```

   (`upstream` is this repository; the [main README](../README.md) shows how to
   set it up.) Later, `git switch main` takes you back to your exercises, and
   `git switch project` returns to your project.

2. **Copy the template.** Copy `Seminar/ProjectTemplate.lean` to
   `Projects/<YourName>/<Problem>.lean`, for example
   `Projects/AdaLovelace/Sylow56.lean`. Use only letters and digits in both
   names, and start each with a capital letter: they become part of Lean names.
   In your copy, rename the namespace `Seminar.Projects.Template` to
   `Projects.<YourName>`, on the `namespace` line near the top and on the `end`
   line at the bottom.

3. **Do the feasibility check (week 11).** Fill in §0–§5 of your file: the
   problem, a statement that typechecks, the prerequisite audit, the vacuity
   guard, the junk-value audit and three lemma names. Then post them as an
   issue on this repository, using the **Feasibility check** form
   (**Issues → New issue → Feasibility check**). Everyone reads and comments on
   these during week 11.

4. **Develop the proof** in §6 of your file. Work top-down: state the lemmas
   you need with `sorry` as their proofs, prove the main theorem from them, and
   then prove the lemmas one at a time. You can split the work into several
   files in your folder.

5. **Check your folder.** From the top folder of the repository, run

   ```bash
   scripts/check.sh Projects/<YourName>
   ```

   It builds the whole repository, then lists every `sorry` left in your
   folder, and any `axiom` or `native_decide`. (Both of those let a proof rest
   on something other than Lean's own checker.) It ends with `PASS` when your
   folder has none of these.

6. **Open a pull request** from the `project` branch of your fork to this
   repository. A pull request asks for your changes to be added here. Commit
   your work, send it to your fork with `git push -u origin project`, and
   GitHub then offers a button to open the pull request. A *draft* pull request
   early on is welcome: others can see your work and help, and GitHub builds it
   for you.

## Partial results

Honest partial results are welcome. If a `sorry` remains, list it in your pull
request and say what it stands for: the statement it leaves unproved, and why
you believe that statement is true. A clearly marked gap is worth more than a
proof that only looks finished.

## What GitHub checks

GitHub builds every pull request. The build must succeed, because this shared
repository must always compile. GitHub then runs `scripts/check.sh Projects`
and shows its report, including any `sorry` that remains. The report is
feedback for you; it does not block the pull request.
