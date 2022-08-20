# GKR_approx_code
This in an experimental code for GKR on Approximate Computation.

## Requirements
One needs NTL (https://www.shoup.net/ntl/) & GMP (https://gmplib.org/) library. \
Installation Guide (GMP)
1. Download gmp-6.2.1.tar.lz and ntl-11.5.1.tar.gz files from the websites.
2. Unpack with tar --lzip -xvf gmp-6.2.1.tar.lz
3. cd ./gmp-6.1.2
./configure
make
make check
sudo make install





We included txt file for polynomial (Lowest Digit Removal polynomial) used in protocol with given parameter. \
To change parameter(Prime, E), one needs to calculate coefficient of polynomials commenting in "genLowDigitPoly(i);" in main.			

## How to run (Need NTL & GMP)
g++ (test_name).cpp -o test -lm -lntl -gmp -pthread -O3 -std=c++11 \
./test (number)

In (test_name), input name of test. \
In (number), input log (number of rounding gates or column length of matrix).
