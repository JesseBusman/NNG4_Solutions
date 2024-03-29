# NNG4 Solutions
You can play the Natural Number Game here: [https://adam.math.hhu.de/#/g/leanprover-community/NNG4](https://adam.math.hhu.de/#/g/leanprover-community/NNG4)

Note that the actual Lean 4 syntax is somewhat different from the commands used in the game.

To set up a Lean 4 environment:
- On linux, run (don't sudo):

  `curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh`
- In Code-OSS or VSCode install the `lean4` extension

To create a new project that depends on the `Mathlib` library (which you will almost definitely want):
- Create a folder `PROJECTNAME` for your project
- `cd PROJECTNAME` into the folder
- Run `lake init PROJECTNAME math`
- Run `lake exe cache get`
- Open your project folder in Code-OSS / VSCode
- To build your project run `lake build`

The NNG4 repository can be found here: [https://github.com/leanprover-community/NNG4/](https://github.com/leanprover-community/NNG4/)
