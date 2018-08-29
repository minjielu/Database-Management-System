This repository contains codes of realizing a basic database management system.

This programming project was done when I didn't have too much coding experience. So coding habit in the repository is very bad, especially that codes are written in .h file.

Nevertheless, this is the most intensive coding experience I have ever had. More than 6000 lines are finished in slightly more than 2 weeks.

Contents:
     
     1. 'myParser.h' contains codes that compile database command texts to a parse tree.
     2. 'myOptimization.h' contains codes that optimize the parse tree to a physical query plan, including pushing down                selection operations, ordering join operations using dynamic programming and so on.
     3. 'myExecution.h' contains codes that execute database commands. One-pass algorithms and two-pass algorithms are
         implemented to reduce disk I/O.
