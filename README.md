# GKR_approx_code
This in an experimental code for GKR on Approximate Computation.

## Requirements
One needs NTL & GMP library. (https://www.shoup.net/ntl/) \
We included txt file for polynomial (Lowest Digit Removal polynomial) used in protocol with given parameter. \
To change parameter(Prime, E), one need to calculate coefficient of polynomials commenting in "genLowDigitPoly(i);" in main.			

## How to run (Need NTL & GMP)
g++ test_name.cpp -o test -lm -lntl -gmp -pthread -O3 -std=c++11 \
./test (number)

in (number), input log (number of rounding gates or column length of matrix).
