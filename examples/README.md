# Our Case Studies
We have tested UKano on several real-world case studies.
This folder contains all ProVerif models for which unlinkability
and anonymity can be automaticaly established orusing UKano.
It also contains protocols wit hattacks.
They all have a dedicatd folder in [`./examples/`](./examples).

We list them all in the [next section](#list-of-case-studies) and provide
benchmarks in section [Benchmarks](#benchmarks).

Finally, note that for some protocols, you need to use specific idealizations
heuristics as explained in the [dedicated section of the wiki](https://github.com/LCBH/UKano/wiki#idealizations-heuristics).
We also list in section [Benchmarks](#benchmarks) the different results
(conclusion and time needed to conclude) one obtain depending on the chosen heuristics.

Remark that, in some files, we may use multiple conditionals in a row to ease the readability.
Note that UKano considers them as a single compacted conditional. We also show how
UKano detects some attacks (for files whose name contains 'attack').


## List of Case Studies
See the table below. References to the protocols can be found at [HBD17].

Legend:
- :white_check_mark: : means that the corresponding condition or property could be automaticaly established using UKano
- :x: : when a condition fails to hold or could not be established
- :fire: : when an attack has been found

| Protocol | Frame-Opacity | Well-Authentication | Unlinkability |
|:---------|:-------------:|:-------------------:|:-------------:|
| Hash-Lock | :white_check_mark: | :white_check_mark: | :white_check_mark: |
| LAK (stateless) | --  | :x: | :fire: |
| Fixed LAK | :white_check_mark: | :white_check_mark: | :white_check_mark: |
| BAC       | :white_check_mark: | :white_check_mark: | :white_check_mark: |
| BAC+ PA+ AA | :white_check_mark: | :white_check_mark: | :white_check_mark: |
| PACE (faillible dec) |  -- | :x: | :fire: |
| PACE (as in~[BFK-09](#references))     |  -- | :x: | :fire: |
| PACE | -- | :x: | :fire: |
| PACE with tags | :white_check_mark: | :white_check_mark: | :white_check_mark: |
| DAA sign | :white_check_mark: | :white_check_mark: | :white_check_mark: |
| DAA join | :white_check_mark: | :white_check_mark: | :white_check_mark: |
| abcdh (irma) | :white_check_mark: | :white_check_mark: | :white_check_mark: |


## Benchmarks
All benchmarks are performed using UKano v0.2 without user-defined idealizations.
The verification is thus truly fully automatic.

Here are the specs of the machine we used:
We performed those benchmarks on this machine:
- OS: Linux sume 3.10-2-amd64 #1 SMP Debian 3.10.5-1 (2013-08-07) x86_64 GNU/Linux
- CPU: Intel(R) Xeon(R) CPU X5650 @ 2.67GHz / stepping: 2 / microcode: 0x13 / cpu MHz: 2659.937 / cache size: 12288 KB
- RAM: 47GO
	    
Legend: time in seconds when verification was successful and :x: when condition could not be established.
THE TABLE IS WIP !

| Protocol    | Better time (total) | Time for WA | Time for FO (greedy) | Time for FO (default) | Time for FO (syntax)  |
|:------------|:-------------:|:-------------------:|:-------------------:|:---------------------:|:--------------------:|:
| Hash-Lock   | ?      | 0.01s | 0.02s  | ?       | ?       |
| Fixed LAK   | ?      | 0.10s | 0.02s  | ?       | ?       |
| BAC         | 70.65s | 0.10s | 70.55s | 262.70s | 256.80s | 
| DAA simplified [HBD17] | 0.12s | 0.02s | 0.10s | 0.10s | 0.10s |
| DAA sign    | 0.58s  | 0.07s | 0.54s  | :x:     | :x:     |
| DAA join    | 35.90s | 13.18s| 22.72s | 22.72s  | 67.49s  |
| abcdh (irma)| ?      | ?     | ?      | ?       | ?  -    |


## References
[HBD17]: L. Hirschi, D. Baelde and S. Delaune.
     A Method for Verifying Privacy-Type Properties : The Unbounded Case.
     Journal version under submission.
     A copy will soon be available at http://projects.lsv.ens-cachan.fr/ukano/.

