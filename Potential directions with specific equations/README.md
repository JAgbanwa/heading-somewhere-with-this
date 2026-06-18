## Wave 1

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
 computations on all 8 cores of my M1 Pro, running this command on Terminal

 ```bash
 ls -lh ~/s3c_sweep/sweep_*.txt
 ```
yields 

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


## Wave 2

```bash
Sweeping |m| in [10000000000,100000000000] on 8 cores
Started: Thu 18 Jun 2026 17:00:57 CEST
  Core 0: [10000000000,21249999999] -> sweep_10000000000_21249999999.txt
  Core 1: [21250000000,32499999999] -> sweep_21250000000_32499999999.txt
  Core 2: [32500000000,43749999999] -> sweep_32500000000_43749999999.txt
  Core 3: [43750000000,54999999999] -> sweep_43750000000_54999999999.txt
  Core 4: [55000000000,66249999999] -> sweep_55000000000_66249999999.txt
  Core 5: [66250000000,77499999999] -> sweep_66250000000_77499999999.txt
  Core 6: [77500000000,88749999999] -> sweep_77500000000_88749999999.txt
  Core 7: [88750000000,99999999999] -> sweep_88750000000_99999999999.txt
```
Running this command
```bash
cat ~/s3c_sweep/sweep_32500000000_43749999999.txt
```
after 8+ hours returned ```167163 -33373801909 235738065125780169```.
