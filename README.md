## SpreadsheetEncoder:
I implemented a Viper frontend for managing spreadsheet data. Utilizing Haskell, I developed an application that interprets and encodes spreadsheet cells into Viper code, ensuring they conform to specifications for verification using backends like Silicon or Carbon.

### Key Features
Spreadsheet Handling: The spreadsheets in this project consist of various cell types including constants, user inputs, and programmatically defined cells with specific pre and postconditions. My implementation focuses on accurately interpreting these cells and transforming them into a format compatible with Viper.
I chose Haskell for the implementation due to its powerful features for handling functional programming constructs, which are ideal for the structured transformation and encoding tasks required by this project.

### Installation and Usage
Setup: Follow the recommended installation process for Haskell using GHCup, though a direct Haskell package from your OS distribution may also be suitable. Ensure that the Viper IDE extension for VS Code is installed and up to date.
Running the Code: To compile the project, use ghc -o Project.o Main.hs from the project directory. You can run the interpreter using ./Project.o run <path/to/example.spr>. Other commands are available and can be explored by running ./Project.o without arguments.
