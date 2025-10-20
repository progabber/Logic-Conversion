# Logic-Conversion
Given a formula in CNF (Conjunctive Normal Form), model it into a formula using only NAND gates with arbitrary fan-in while minimising number of gates used.

## How to use:
Enter the number of clauses 'n' in the given CNF formula in the first line. <br>
This is followed by 'n' lines each containing a strictly positive or negative number representing a proposition or its negation (e.g. 1 -4 3 represents p_1 AND ~p_4 AND p_3). <br>
The program then outputs the minimum number of NAND gates required to model the CNF along with the connections required.
