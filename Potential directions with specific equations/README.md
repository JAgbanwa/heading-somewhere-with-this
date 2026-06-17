```bash
Started: Tue 16 Jun 2026 20:53:46 CEST
  Core 0: [2814000000,3712249999] -> sweep_2814000000_3712249999.txt
  Core 1: [3712250000,4610499999] -> sweep_3712250000_4610499999.txt
  Core 2: [4610500000,5508749999] -> sweep_4610500000_5508749999.txt
  Core 3: [5508750000,6406999999] -> sweep_5508750000_6406999999.txt
  Core 4: [6407000000,7305249999] -> sweep_6407000000_7305249999.txt
  Core 5: [7305250000,8203499999] -> sweep_7305250000_8203499999.txt
  Core 6: [8203500000,9101749999] -> sweep_8203500000_9101749999.txt
  Core 7: [9101750000,9999999999] -> sweep_9101750000_9999999999.txt
Running... do not close terminal
```

After 12+ hours of running [these](https://github.com/JAgbanwa/heading-somewhere-with-this/tree/main/Potential%20directions%20with%20specific%20equations/s3c_sweep)
 computations on all 8 cores of my M1 Pro on Terminal, this was the outcome:

 ```ls -lh ~/s3c_sweep/sweep_*.txt```

```bash
-rw-r--r--  1 jamalmac  staff    34B 17 Jun 00:16 /Users/jamalmac/s3c_sweep/sweep_2814000000_3712249999.txt
-rw-r--r--  1 jamalmac  staff    36B 16 Jun 21:19 /Users/jamalmac/s3c_sweep/sweep_3712250000_4610499999.txt
-rw-r--r--  1 jamalmac  staff     0B 16 Jun 20:53 /Users/jamalmac/s3c_sweep/sweep_4610500000_5508749999.txt
-rw-r--r--  1 jamalmac  staff     0B 16 Jun 20:53 /Users/jamalmac/s3c_sweep/sweep_5508750000_6406999999.txt
-rw-r--r--  1 jamalmac  staff     0B 16 Jun 20:53 /Users/jamalmac/s3c_sweep/sweep_6407000000_7305249999.txt
-rw-r--r--  1 jamalmac  staff     0B 16 Jun 20:53 /Users/jamalmac/s3c_sweep/sweep_7305250000_8203499999.txt
-rw-r--r--  1 jamalmac  staff     0B 16 Jun 20:53 /Users/jamalmac/s3c_sweep/sweep_8203500000_9101749999.txt
-rw-r--r--  1 jamalmac  staff     0B 16 Jun 20:53 /Users/jamalmac/s3c_sweep/sweep_9101750000_9999999999.txt
```
This first sweep 

```bash
cat ~/s3c_sweep/sweep_3712250000_4610499999.txt
```
yielded ```-37917 -3798121117 3749549735825673``` and 

```bash
cat ~/s3c_sweep/sweep_2814000000_3712249999.txt
```
yielded ```-6565 -3579502461 672515729205193```
