/* 
Name of program: Assignment4.cpp
Description: Soduku Solver that reads puzzles from text files, solves them, and prints the solutions.
Inputs: Text files containing Sudoku puzzles
Outputs: Terminal messages
All Collaborators: Me, ChatGPT
Author: Bruno Barron Silva
Creation date: 10/13/2026
Revision date: 10/13/2026
Revisions: Error messages now give the row and column of a bad character, the actual cell count of a wrong-sized file, and the location of a conflicting clue.
Used bitmasks for used digits in each row, column, and box, so a candidate check is O(1). The search now fills the most-constrained empty cell first and abandons a branch when any cell has no candidates.
Solutions are printed as they are found instead of stored, so extra memory is O(1). The grid is a flat std::array.
The search reports solutions through a callback instead of printing, the bitmask logic is in small helper methods, and filenames can be given on the command line (the five default files are used if none are given).
*/
// Include the tools this program needs, each with the reason it is needed.
#include <array> // Provides std::array for fixed-size grids and bitmask tables.
#include <bitset> // Provides std::bitset to count how many candidates a cell has.
#include <cctype> // Provides std::isspace for ignoring whitespace in puzzle files.
#include <cstddef> // Provides std::size_t for solution counts.
#include <cstdint> // Provides std::uint16_t for compact bitmasks.
#include <fstream> // Provides std::ifstream for opening and reading files.
#include <functional> // Provides std::function so the search can report solutions without printing.
#include <iostream> // Provides std::cout and std::cerr for displaying output and errors.
#include <string> // Provides std::string for filenames and messages.
#include <utility> // Provides std::swap for reordering the list of empty cells.
#include <vector> // Provides std::vector for the list of filenames.
 
// Define a class that keeps the Sudoku grid and solving behavior together.
class SudokuSolver { // Start of the object-oriented Sudoku solver class.
private: // Keep the grid and helper methods internal to this class.
    static constexpr int SIZE = 9; // Number of rows and columns in a Sudoku grid.
    static constexpr int BOX_SIZE = 3; // Width and height of each 3-by-3 box.
    static constexpr int CELLS = SIZE * SIZE; // Total number of cells (81).
    using Mask = std::uint16_t; // A bitmask where bit d is set when digit d is used (bits 1-9).
    static constexpr Mask ALL_DIGITS = 0x3FE; // Bits 1 through 9 set: every digit is a candidate.
    using Grid = std::array<int, CELLS>; // A flat, row-major grid; 0 means blank, 1-9 are digits.
    using SolutionHandler = std::function<void(const Grid&, std::size_t)>; // Called once for each solution found.
 
    Grid grid{}; // The current puzzle, filled in and undone as the search runs.
    std::array<Mask, SIZE> rowUsed{}; // Digits already used in each row.
    std::array<Mask, SIZE> colUsed{}; // Digits already used in each column.
    std::array<Mask, SIZE> boxUsed{}; // Digits already used in each 3-by-3 box.
    std::array<int, CELLS> empties{}; // Indices of the blank cells; the search reorders this list.
    int emptyCount = 0; // How many blank cells the puzzle has.
    std::size_t solutionCount = 0; // How many solutions the search has found so far.
 
    int boxOf(int row, int col) const { // Convert a row and column into a box number 0-8.
        return (row / BOX_SIZE) * BOX_SIZE + (col / BOX_SIZE); // Boxes are numbered left to right, top to bottom.
    } // End of boxOf.
 
    Mask candidatesFor(int cell) const { // Find every digit that can legally go in one cell.
        int row = cell / SIZE; // Row of this cell.
        int col = cell % SIZE; // Column of this cell.
        Mask used = rowUsed[row] | colUsed[col] | boxUsed[boxOf(row, col)]; // Combine digits used in the row, column, and box.
        return static_cast<Mask>(ALL_DIGITS & ~used); // Candidates are the digits that are not used anywhere.
    } // End of candidatesFor.
 
    bool prepareSearch(std::string& conflictMessage) { // Build the bitmasks and check the given clues.
        rowUsed.fill(0); // Forget any digits recorded for a previous puzzle.
        colUsed.fill(0); // Forget any digits recorded for a previous puzzle.
        boxUsed.fill(0); // Forget any digits recorded for a previous puzzle.
        emptyCount = 0; // Restart the list of blank cells.
        for (int cell = 0; cell < CELLS; ++cell) { // Visit every cell in reading order.
            int value = grid[cell]; // Read the digit (or 0) stored in this cell.
            if (value == 0) { // Check whether this cell is blank.
                empties[emptyCount++] = cell; // Remember the blank cell so the search can fill it later.
                continue; // Blank cells cannot conflict with anything.
            } // Finish handling a blank cell.
            int row = cell / SIZE; // Row of this given digit.
            int col = cell % SIZE; // Column of this given digit.
            int box = boxOf(row, col); // Box of this given digit.
            Mask bit = static_cast<Mask>(1u << value); // Bit that represents this digit.
            if ((rowUsed[row] | colUsed[col] | boxUsed[box]) & bit) { // Check whether the digit repeats in its row, column, or box.
                conflictMessage = "digit " + std::to_string(value) + " at row " + std::to_string(row + 1) // Start describing the conflict.
                                  + ", column " + std::to_string(col + 1) + " repeats in its row, column, or box"; // Finish describing it.
                return false; // Report that the given clues contradict each other.
            } // Finish handling a conflicting digit.
            rowUsed[row] |= bit; // Record the digit as used in its row.
            colUsed[col] |= bit; // Record the digit as used in its column.
            boxUsed[box] |= bit; // Record the digit as used in its box.
        } // Finish checking every cell.
        return true; // Confirm that all given digits are consistent.
    } // End of prepareSearch.
 
    void search(int depth, const SolutionHandler& onSolution) { // Recursively fill blank cells using backtracking.
        if (depth == emptyCount) { // Check whether every blank cell has been filled.
            ++solutionCount; // Count this complete solution.
            onSolution(grid, solutionCount); // Hand the solution to the caller instead of printing here.
            return; // End this recursive path because the grid is solved.
        } // Finish handling a completed grid.
        int bestIndex = depth; // Position in the list of the most-constrained blank cell found so far.
        int bestCount = SIZE + 1; // Start above the maximum so any real cell beats it.
        Mask bestMask = 0; // Candidates of the most-constrained cell found so far.
        for (int i = depth; i < emptyCount; ++i) { // Examine every blank cell that is still unfilled.
            Mask mask = candidatesFor(empties[i]); // Find the legal digits for this blank cell.
            int count = static_cast<int>(std::bitset<16>(mask).count()); // Count how many legal digits it has.
            if (count == 0) { // Check whether this cell has no legal digit at all.
                return; // Abandon this branch immediately because it cannot lead to a solution.
            } // Finish handling a dead end.
            if (count < bestCount) { // Check whether this cell is more constrained than the best so far.
                bestCount = count; // Remember how constrained it is.
                bestIndex = i; // Remember where it is in the list.
                bestMask = mask; // Remember its candidates.
                if (count == 1) { // Check whether the cell has exactly one choice.
                    break; // Stop looking because a forced cell cannot be beaten.
                } // Finish handling a forced cell.
            } // Finish comparing against the best cell.
        } // Finish looking for the most-constrained cell.
        std::swap(empties[depth], empties[bestIndex]); // Move the chosen cell to the current depth in the list.
        int cell = empties[depth]; // Read the cell this level will fill.
        int row = cell / SIZE; // Row of the chosen cell.
        int col = cell % SIZE; // Column of the chosen cell.
        int box = boxOf(row, col); // Box of the chosen cell.
        for (int digit = 1; digit <= SIZE; ++digit) { // Try each possible digit from 1 through 9.
            Mask bit = static_cast<Mask>(1u << digit); // Bit that represents this digit.
            if (!(bestMask & bit)) { // Check whether this digit is not a legal candidate.
                continue; // Skip it without re-checking the row, column, and box.
            } // Finish skipping an illegal digit.
            grid[cell] = digit; // Tentatively place this candidate in the cell.
            rowUsed[row] |= bit; // Mark the digit as used in the row.
            colUsed[col] |= bit; // Mark the digit as used in the column.
            boxUsed[box] |= bit; // Mark the digit as used in the box.
            search(depth + 1, onSolution); // Recursively try to complete the grid with this candidate.
            grid[cell] = 0; // Undo the tentative choice in the grid.
            rowUsed[row] ^= bit; // Free the digit in the row.
            colUsed[col] ^= bit; // Free the digit in the column.
            boxUsed[box] ^= bit; // Free the digit in the box.
        } // Finish trying all candidates for this cell.
    } // End of search.
 
    void printGrid(const Grid& board) const { // Print a grid in a readable Sudoku layout.
        for (int row = 0; row < SIZE; ++row) { // Print the grid one row at a time.
            if (row > 0 && row % BOX_SIZE == 0) { // Check whether a horizontal box divider belongs before this row.
                std::cout << "------+-------+------\n"; // Separate the three horizontal bands of boxes.
            } // Finish checking for a horizontal divider.
            for (int col = 0; col < SIZE; ++col) { // Print every cell in the current row.
                if (col > 0 && col % BOX_SIZE == 0) { // Check whether a vertical box divider belongs here.
                    std::cout << "| "; // Separate the three vertical boxes.
                } // Finish checking for a vertical divider.
                int value = board[row * SIZE + col]; // Read the cell from the flat grid.
                if (value == 0) { // Check whether the cell is blank.
                    std::cout << "_ "; // Show an underscore for an empty cell.
                } else { // Handle a cell containing a digit.
                    std::cout << value << ' '; // Print the digit followed by a space.
                } // Finish printing this cell.
            } // Finish printing all cells in this row.
            std::cout << '\n'; // Move to the next output line after this row.
        } // Finish printing all nine rows.
    } // End of printGrid.
 
public: // Expose the operations that main needs to use.
    bool loadFromFile(const std::string& filename) { // Load a puzzle file and check its format.
        std::ifstream inputFile(filename); // Attempt to open the requested puzzle file.
        if (!inputFile) { // Check whether the file could not be opened.
            std::cerr << "Error: could not open " << filename << ".\n"; // Explain which file failed to open.
            return false; // Tell the caller that loading failed.
        } // Finish handling an open failure.
        Grid loaded{}; // Read into a temporary grid so a bad file never changes the current puzzle.
        int cellCount = 0; // Count how many cell symbols have been read so far.
        char character; // Hold each character read from the input file.
        while (inputFile.get(character)) { // Read the file one character at a time.
            if (std::isspace(static_cast<unsigned char>(character))) { // Ignore spaces, tabs, and newline characters.
                continue; // Move to the next character without treating whitespace as a cell.
            } // Finish skipping whitespace.
            if (cellCount == CELLS) { // Check whether the file has a symbol beyond the 81st cell.
                std::cerr << "Error: " << filename << " contains more than 81 cells.\n"; // Explain the excessive cell count.
                return false; // Reject a puzzle with too many cells.
            } // Finish checking the maximum number of cells.
            int value = 0; // Hold the numeric value of this cell (0 for blank).
            if (character == '_') { // Check whether the character marks a blank cell.
                value = 0; // Store zero internally to represent the blank.
            } else if (character >= '1' && character <= '9') { // Check whether the character is a valid Sudoku digit.
                value = character - '0'; // Convert the character digit into its integer value.
            } else { // Handle any character that is not whitespace, underscore, or digit 1-9.
                std::cerr << "Error: invalid character '" << character << "' in " << filename // Identify the bad character and file.
                          << " (row " << cellCount / SIZE + 1 << ", column " << cellCount % SIZE + 1 << ").\n"; // Say exactly where it is.
                return false; // Stop loading because the puzzle format is invalid.
            } // Finish interpreting this input character.
            loaded[cellCount++] = value; // Store the cell and advance to the next position.
        } // Finish reading the complete file.
        if (cellCount != CELLS) { // Check whether exactly 81 cells were read.
            std::cerr << "Error: " << filename << " must contain exactly 81 cells but has " << cellCount << ".\n"; // Explain the required size and the actual count.
            return false; // Reject a puzzle that has too few cells.
        } // Finish checking the cell count.
        grid = loaded; // Accept the puzzle by copying the temporary grid into place.
        return true; // Report that the puzzle file was loaded successfully.
    } // End of loadFromFile.
 
    void solveAndPrint(const std::string& filename) { // Solve the loaded puzzle and print its results.
        solutionCount = 0; // Reset the count left over from any previous puzzle.
        std::cout << "\nPuzzle file: " << filename << "\n"; // Display the name of the current puzzle file.
        std::cout << "Original puzzle:\n"; // Label the puzzle as it appeared in the file.
        printGrid(grid); // Display the starting puzzle before attempting to solve it.
        std::string conflictMessage; // Receive a description if the given clues contradict each other.
        if (!prepareSearch(conflictMessage)) { // Build the bitmasks and reject conflicting clues.
            std::cout << "No solution found (the given clues conflict: " << conflictMessage << ").\n"; // Report why there is no solution.
            return; // Skip the search because conflicting clues cannot produce a valid solution.
        } // Finish validating the starting puzzle.
        auto printSolution = [this](const Grid& solved, std::size_t number) { // Define how each solution is displayed.
            std::cout << "\nSolution " << number << ":\n"; // Label the solution with a human-friendly number.
            printGrid(solved); // Print the completed Sudoku grid.
        }; // Finish defining the solution printer.
        search(0, printSolution); // Run the depth-first search; solutions print as they are found.
        if (solutionCount == 0) { // Check whether the search failed to find any complete solution.
            std::cout << "No solution found.\n"; // Print the required message when no solution exists.
            return; // Finish processing this puzzle.
        } // Finish handling the no-solution case.
        std::cout << "\nNumber of solutions found: " << solutionCount << "\n"; // Report how many solutions were discovered.
    } // End of solveAndPrint.
}; // End of the SudokuSolver class.
 
// Define the program's entry point, where execution begins.
int main(int argc, char* argv[]) { // Accept optional puzzle filenames from the command line.
    std::vector<std::string> filenames; // Hold the puzzle files to process.
    for (int i = 1; i < argc; ++i) { // Visit each command-line argument.
        filenames.push_back(argv[i]); // Treat each argument as a puzzle filename.
    } // Finish collecting command-line filenames.
    if (filenames.empty()) { // Check whether the user gave no filenames.
        filenames = {"puzzle1.txt", "puzzle2.txt", "puzzle3.txt", "puzzle4.txt", "puzzle5.txt"}; // Fall back to the five files the assignment requires.
    } // Finish choosing the default filenames.
    SudokuSolver solver; // Create one solver object to process each puzzle in sequence.
    bool allLoaded = true; // Track whether every puzzle file could be loaded.
    for (const std::string& filename : filenames) { // Process each puzzle file.
        if (solver.loadFromFile(filename)) { // Continue only if the current file was read successfully.
            solver.solveAndPrint(filename); // Print the original puzzle and every solution found.
        } else { // Handle a file that could not be loaded or had an invalid format.
            std::cout << "Skipping " << filename << " because it could not be loaded.\n"; // Explain why this puzzle was skipped.
            allLoaded = false; // Remember that at least one file failed.
        } // Finish handling the current file's loading result.
    } // Finish processing all puzzle files.
    return allLoaded ? 0 : 1; // Return a nonzero exit status if any file failed to load.
} // End of main.