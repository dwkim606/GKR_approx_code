# GKR_approx_code
This in an experimental code for GKR on Approximate Computation.

## Requirements
Needs NTL (https://www.shoup.net/ntl/) & GMP (https://gmplib.org/) library. \
Installation Guide (GMP)
1. Download gmp-6.2.1.tar.lz from the website.
2. Unpack with the command: tar --lzip -xvf gmp-6.2.1.tar.lz
3. Build and Install 
```console
cd ./gmp-6.2.1
./configure
make
make check
sudo make install
```

Installation Guide (NTL)
1. Download ntl-11.5.1.tar.gz from the website.
2. Unpack with the command tar -xvf ntl-11.5.1.tar.gz
3. Build and Install
```console
cd ./ntl-11.5.1/src
./configure NTL_THREADS=on NTL_THREAD_BOOST=on NTL_EXCEPTIONS=on SHARED=on NTL_STD_CXX11=on NTL_SAFE_VECTORS=off TUNE=generic
make
make check
sudo make install
```

## How to run (Need NTL & GMP)
g++ (test_name).cpp -o test -lm -lntl -lgmp -pthread -O3 -std=c++11 \
./test (number)

In (test_name), input name of test. \
In (number), input log (number of rounding gates or column length of matrix).

We included txt file for polynomial (Lowest Digit Removal polynomial) used in protocol with given parameter. \
To change parameter(Prime, E), one needs to calculate coefficient of polynomials commenting in "genLowDigitPoly(i);" in main.			
