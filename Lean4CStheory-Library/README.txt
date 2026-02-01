Steps to Use This Lean Project

Step 1 – Install elan (Lean version manager)
Install elan by following the instructions for your operating system:
https://github.com/leanprover/elan?tab=readme-ov-file#installation

Elan automatically manages Lean and Lake versions.

Step 2 – Verify installation
Open a terminal and run:
elan --version

If this prints a version number, elan is installed correctly.

Step 3 – Download dependencies, cache, and build the project
Open a terminal in the project root folder (the folder containing lakefile.lean).

Run the following commands in order:
lake update
lake exe cache get
lake build

These commands automatically:
- Install the correct Lean version using lean-toolchain
- Download the precompiled mathlib cache
- Build the project

Step 4 – Install Visual Studio Code (skip if already installed)
Download and install VS Code from:
https://code.visualstudio.com/download

Step 5 – Install Lean 4 extension in VS Code
Open VS Code, go to Extensions, and install “Lean 4” (by leanprover).

Step 6 – Open and check the project in VS Code
1. Open VS Code
2. Open the project root folder (the folder with lakefile.lean)
3. Open the file:
   exercises/ClassTasks/Alg_Task1_Lean4.lean

The Lean server should start automatically, and Lean InfoView should appear.

Warning:
If you see mathlib being rebuilt in InfoView:
1. Close VS Code
2. Delete the .lake folder in the project root
3. Repeat Step 3
4. Reopen the project in VS Code