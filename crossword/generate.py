import sys
import random
from crossword import *
from collections import deque


class CrosswordCreator():

    def __init__(self, crossword):
        """
        Create new CSP crossword generate.
        """
        self.crossword = crossword
        self.domains = {
            var: self.crossword.words.copy()
            for var in self.crossword.variables
        }

    def letter_grid(self, assignment):
        """
        Return 2D array representing a given assignment.
        """
        letters = [
            [None for _ in range(self.crossword.width)]
            for _ in range(self.crossword.height)
        ]
        for variable, word in assignment.items():
            direction = variable.direction
            for k in range(len(word)):
                i = variable.i + (k if direction == Variable.DOWN else 0)
                j = variable.j + (k if direction == Variable.ACROSS else 0)
                letters[i][j] = word[k]
        return letters

    def print(self, assignment):
        """
        Print crossword assignment to the terminal.
        """
        letters = self.letter_grid(assignment)
        for i in range(self.crossword.height):
            for j in range(self.crossword.width):
                if self.crossword.structure[i][j]:
                    print(letters[i][j] or " ", end="")
                else:
                    print("█", end="")
            print()

    def save(self, assignment, filename):
        """
        Save crossword assignment to an image file.
        """
        from PIL import Image, ImageDraw, ImageFont
        cell_size = 100
        cell_border = 2
        interior_size = cell_size - 2 * cell_border
        letters = self.letter_grid(assignment)

        # Create a blank canvas
        img = Image.new(
            "RGBA",
            (self.crossword.width * cell_size,
             self.crossword.height * cell_size),
            "black"
        )
        font = ImageFont.truetype("assets/fonts/OpenSans-Regular.ttf", 80)
        draw = ImageDraw.Draw(img)

        for i in range(self.crossword.height):
            for j in range(self.crossword.width):

                rect = [
                    (j * cell_size + cell_border,
                     i * cell_size + cell_border),
                    ((j + 1) * cell_size - cell_border,
                     (i + 1) * cell_size - cell_border)
                ]
                if self.crossword.structure[i][j]:
                    draw.rectangle(rect, fill="white")
                    if letters[i][j]:
                        w, h = draw.textsize(letters[i][j], font=font)
                        draw.text(
                            (rect[0][0] + ((interior_size - w) / 2),
                             rect[0][1] + ((interior_size - h) / 2) - 10),
                            letters[i][j], fill="black", font=font
                        )

        img.save(filename)

    def solve(self):
        """
        Enforce node and arc consistency, and then solve the CSP.
        """
        self.enforce_node_consistency()
        self.ac3()
        return self.backtrack(dict())

    def enforce_node_consistency(self):
        """
        Update `self.domains` such that each variable is node-consistent.
        (Remove any values that are inconsistent with a variable's unary
         constraints; in this case, the length of the word.)
        """
        for variable in self.crossword.variables:
            for word in self.domains[variable].copy():
                if len(word) != variable.length:
                    self.domains[variable].discard(word)

    def revise(self, x, y):
        """
        Make variable `x` arc consistent with variable `y`.
        To do so, remove values from `self.domains[x]` for which there is no
        possible corresponding value for `y` in `self.domains[y]`.

        Return True if a revision was made to the domain of `x`; return
        False if no revision was made.
        """
        if x == y:
            return False
        
        overlaps = self.crossword.overlaps[x, y]
        if overlaps is None:
            return False

        revised = False
        for x_word in self.domains[x].copy():
            hypothetical_assignment = {}
            hypothetical_assignment[x] = x_word
            has_corresponding_value = False
            for y_word in self.domains[y]:
                hypothetical_assignment[y] = y_word
                if not self.do_variable_assignments_conflict(hypothetical_assignment):
                    has_corresponding_value = True
                hypothetical_assignment.pop(y)
            if not has_corresponding_value:
                self.domains[x].discard(x_word)
                revised = True
            hypothetical_assignment.pop(x)
        return revised
        

    def ac3(self, arcs=None):
        """
        Update `self.domains` such that each variable is arc consistent.
        If `arcs` is None, begin with initial list of all arcs in the problem.
        Otherwise, use `arcs` as the initial list of arcs to make consistent.

        Return True if arc consistency is enforced and no domains are empty;
        return False if one or more domains end up empty.
        """
        # TODO: optimize by caching neighbors
        if arcs is None:
            arcs = deque()
            for node in self.crossword.variables:
                for neighbor in self.crossword.neighbors(node):
                    arc = (node, neighbor)
                    arcs.append(arc)
        
        while arcs:
            arc = arcs.popleft()
            if self.revise(arc[0], arc[1]):
                if len(self.domains[arc[0]]) == 0:
                    return False
                for neighbor in self.crossword.neighbors(arc[0]):
                    if neighbor != arc[0] and neighbor != arc[1]:
                        arcs.append((arc[0], neighbor))

        return True

    def assignment_complete(self, assignment):
        """
        Return True if `assignment` is complete (i.e., assigns a value to each
        crossword variable); return False otherwise.
        """
        if len(assignment) == len(self.crossword.variables):
            return True
        return False

    def consistent(self, assignment):
        """
        Return True if `assignment` is consistent (i.e., words fit in crossword
        puzzle without conflicting characters); return False otherwise.
        """
        # Check if the assignment is consistent in O(n):
        assignment_values = set()
        for variable in assignment:

            # 1) Ensure all values are distinct:
            if assignment[variable] in assignment_values:
                return False
            assignment_values.add(assignment[variable])

            # 2) Ensure every value is the correct length:
            # Note: this will check the length, direction, and starting point.
            if variable not in self.crossword.variables:
                return False

        # 3) Ensure there are no conflicts between neighboring variables:
        if self.do_variable_assignments_conflict(assignment):
            return False
        return True

    def do_variable_assignments_conflict(self, assignment):
        """
        Checks the overlap cells between all variables within an assignment to check for conflicting values.
        Returns True if there are no value conflicts in overlapping cells.
        Returns False if any assigned variable has a conflicting character with another variable in the same crossword cell.
        """
        for x in assignment:
            for y in assignment:
                if x != y:
                    overlaps = self.crossword.overlaps[x, y]
                    if overlaps is not None:
                        if assignment[x][overlaps[0]] != assignment[y][overlaps[1]]:
                            return True
        return False

    def order_domain_values(self, var, assignment):
        """
        Return a list of values in the domain of `var`, in order by
        the number of values they rule out for neighboring variables.
        The first value in the list, for example, should be the one
        that rules out the fewest values among the neighbors of `var`.
        """
        """
        # TODO: this is a heuristic one
        TODO
        The order_domain_values function should return a list of all of the values in the domain of var, ordered according to the least-constraining values heuristic.

var will be a Variable object, representing a variable in the puzzle.
Recall that the least-constraining values heuristic is computed as the number of values ruled out for neighboring unassigned variables. That is to say, if assigning var to a particular value results in eliminating n possible choices for neighboring variables, you should order your results in ascending order of n.
Note that any variable present in assignment already has a value, and therefore shouldn’t be counted when computing the number of values ruled out for neighboring unassigned variables.
For domain values that eliminate the same number of possible choices for neighboring variables, any ordering is acceptable.
Recall that you can access self.crossword.overlaps to get the overlap, if any, between two variables.
It may be helpful to first implement this function by returning a list of values in any arbitrary order (which should still generate correct crossword puzzles). Once your algorithm is working, you can then go back and ensure that the values are returned in the correct order.
You may find it helpful to sort a list according to a particular key: Python contains some helpful functions for achieving this.
        """
        # print(f"order_domain_values({var}, {assignment})")
        print(f"order_domain_values({var})")
        ordered_domain_values = []
        # print("domain: ", self.domains[var])
        for value in self.domains[var]:
            ordered_domain_values.append(value)
        
        print("ordered_domain_values: ", ordered_domain_values)
        return ordered_domain_values

    def select_unassigned_variable(self, assignment):
        """
        Return an unassigned variable not already part of `assignment`.
        Choose the variable with the minimum number of remaining values
        in its domain. If there is a tie, choose the variable with the highest
        degree. If there is a tie, any of the tied variables are acceptable
        return values.
        """
        """
        # TODO: this is a heuristic one
        TODO
        The select_unassigned_variable function should return a single variable in the crossword puzzle that is not yet assigned by assignment, according to the minimum remaining value heuristic and then the degree heuristic.

An assignment is a dictionary where the keys are Variable objects and the values are strings representing the words those variables will take on. You may assume that the assignment will not be complete: not all variables will be present in the assignment.
Your function should return a Variable object. You should return the variable with the fewest number of remaining values in its domain. If there is a tie between variables, you should choose among whichever among those variables has the largest degree (has the most neighbors). If there is a tie in both cases, you may choose arbitrarily among tied variables.
It may be helpful to first implement this function by returning any arbitrary unassigned variable (which should still generate correct crossword puzzles). Once your algorithm is working, you can then go back and ensure that you are returning a variable according to the heuristics.
You may find it helpful to sort a list according to a particular key: Python contains some helpful functions for achieving this.
        """
        #print(f"select_unassigned_variable({assignment})")

        variables_not_in_assigment = set()
        for variable in self.crossword.variables:
            if variable not in assignment:
                variables_not_in_assigment.add(variable)

        choice = random.choice(list(variables_not_in_assigment))
        #print("choice: ", choice)
        return choice

    def backtrack(self, assignment):
        """
        Using Backtracking Search, take as input a partial assignment for the
        crossword and return a complete assignment if possible to do so.

        `assignment` is a mapping from variables (keys) to words (values).

        If no assignment is possible, return None.
        """
        if self.assignment_complete(assignment):
            return assignment
        variable = self.select_unassigned_variable(assignment)
        for value in self.order_domain_values(variable, assignment):
            if value not in assignment:
                assignment[variable] = value
                result = self.backtrack(assignment)
                if self.assignment_complete(assignment) and self.consistent(assignment):
                    return result
            assignment.pop(variable)

        return None

def main():

    # Check usage
    if len(sys.argv) not in [3, 4]:
        sys.exit("Usage: python generate.py structure words [output]")

    # Parse command-line arguments
    structure = sys.argv[1]
    words = sys.argv[2]
    output = sys.argv[3] if len(sys.argv) == 4 else None

    # Generate crossword
    crossword = Crossword(structure, words)
    creator = CrosswordCreator(crossword)
    assignment = creator.solve()

    # Print result
    if assignment is None:
        print("No solution.")
    else:
        creator.print(assignment)
        if output:
            creator.save(assignment, output)


if __name__ == "__main__":
    main()
