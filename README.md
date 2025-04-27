# TASE25-Artifact
This is the artifact of the TASE25 paper "A Formal Framework for Naturally Specifying and Verifying Sequential Algorithms".

## Code Structure
Directories/files denoted with `*` are not within the scope of this paper.
```
.
├── sets*         # Dependency: Library for set theory
├── fixedpoints*  # Dependency: Library for order theory and fixed points
├── monadlib      # Core Monad Library
│   ├── set_monad      # Set Monad
│   │   ├── Monad.v        # Monad definitions and notations
│   │   ├── SetBasic.v     # Constructors and properties
│   │   └── SetHoare.v     # Hoare logic and tactics
│   ├── state_rel_monad    # State Relation Monad
│   │   ├── StateRelBasic.v    # Constructors and properties
│   │   ├── StateRelHoare.v    # Hoare logic and tactics
│   │   └── safeexec_lib.v*    # library for relational Hoare Logic
│   └── monad_err          # Monad with Error
│       ├── MonadErrBasic.v    # Basic constructors and properties
│       ├── MonadErrLoop.v     # Loop constructors and properties
│       ├── MonadErrHoare.v    # Hoare logic and tactics
│       └── monadsafe_lib.v*   # library for relational Hoare Logic
└── examples
    ├── DFS.v         # DFS example in State Relation Monad
    ├── KMP.v         # Two-stage proof for the KMP algorithm in Set Monad
    ├── Listlib.v*    # List lemmas for the KMP proof
    └── KMPErr.v      # Definition of the KMP algorithm in the Monad with Error
```

## How to Compile
Coq version: 8.15.2

Before compiling, you shall first fetch git submodules as follows:
```
git submodule init; git submodule update
```

On Windows, you need to manually provide a CONFIGURE file to specify the paths for the required dependencies. Please create an extensionless file named CONFIGURE in the directory and write the path to your Coq installation into that file. There's no need for a CONFIGURE if you're using a Linux system and coq is in bin search path.

For example, in a cygwin build environment, the CONFIGURE file is set as follows:

```
COQBIN=/cygdrive/d/Coq-8.15/bin/
SUF=   # Here, you can also set SUF=.exe
```

If your build environment is Windows PowerShell, use the following CONFIGURE settings:

```
COQBIN=D:\Coq-8.15\bin\\
SUF=.exe
```

Before compiling, please first check whether your environment has make installed by running:

```
make --version
```

If not, you can use mingw32-make or mingw64-make as an alternative (make sure that they are installed):

```
mingw32-make --version
or
mingw64-make --version
```

Then, you can start compiling by running:

```
make
```
