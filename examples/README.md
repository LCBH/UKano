# Our Case Studies
We have tested UKano on several real-world case studies.
This folder contains all ProVerif models for which unlinkability
and anonymity can be automaticaly established using UKano.
It also contains protocols with attacks.
They all have a dedicatd folder in [`./examples/`](./examples).

We list them all in the [next section](#list-of-case-studies) and provide
benchmarks in section [Benchmarks](#benchmarks).

Finally, note that for some protocols, you need to use specific idealizations
heuristics as explained in the [dedicated section of the wiki](https://github.com/LCBH/UKano/wiki#idealizations-heuristics).
We also list in section [Benchmarks](#benchmarks) the different results
(conclusion and time needed to conclude) one obtain depending on the chosen heuristic.

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
| BAC+ AA+ PA | :white_check_mark: | :white_check_mark: | :white_check_mark: |
| PACE (faillible dec) |  -- | :x: | :fire: |
| PACE (as in~[BFK-09](#references))     |  -- | :x: | :fire: |
| PACE | -- | :x: | :fire: |
| PACE with tags | :white_check_mark: | :white_check_mark: | :white_check_mark: |
| DAA sign | :white_check_mark: | :white_check_mark: | :white_check_mark: |
| DAA join | :white_check_mark: | :white_check_mark: | :white_check_mark: |
| abcdh (irma) | :white_check_mark: | :white_check_mark: | :white_check_mark: |


## Benchmarks
All benchmarks are performed using UKano v0.2 (with ProVerif v1.92 as backend)
without user-defined idealizations (except for some cases indicated with (*)).
For most cases, the verification is thus truly fully automatic.

Here are the specs of the machine we used:
We performed those benchmarks on this machine:
- OS: Linux sume 3.10-2-amd64 #1 SMP Debian 3.10.5-1 (2013-08-07) x86_64 GNU/Linux
- CPU: Intel(R) Xeon(R) CPU X5650 @ 2.67GHz / stepping: 2 / microcode: 0x13 / cpu MHz: 2659.937 / cache size: 12288 KB
- RAM: 47GO
	    
Legend: time in seconds when verification was successful, :x: when condition
could not be established, :curly_loop: when the verification took too much time (>20 hours) or too
much memory (>20GO of RAM), and, -- when it was not necessary to build idealizations manually
(i.e., user defined). The different columns for FO (i.e., frame opacity) refers to the different
heuristics of UKano to build idealization:
- "greedy" corresponds to the option `--ideal-greedy`
- "default" corresponds to the default heuristics of UKano
- "syntax" corresponds to the option `--ideal-full-syntax`
- "user-defined" when a user defined idealization is necessary


| Protocol    | Better time (total) | Time for WA | Time for FO (greedy) | Time for FO (default) | Time for FO (syntax)  | Time for FO (user-defined) |
|:------------|:-------------:|:-------------------:|:-------------------:|:---------------------:|:--------------------:|:---------------------------|
| Hash-Lock      | 0.00s  | 0.00s | 0.00s  | 0.00s   | 0.00s   | --    |
| Fixed LAK      | 0.00s  | 0.00s | 0.00s  | 0.00s   | 0.00s   | --    |
| BAC            | 8.41s  | 0.02s | 8.39s | 17.24s  | 17.20s  | --    |
| BAC+AA+PA      | 198.28s| 0.42s |197.86s | 1013.56s    | 998.81s    | --    |
| BAC+PA+AA      | 183.40s| 0.33s |183.07s|  1068.79s | 1191.04s   | --    |
| PACE with tags | 169.91 | 62.99s| 106.92s (*) | :curly_loop:   | :curly_loop: |106.92s |
| DAA simplified [HBD17]| 0.02s |0.01s| :x: | 0.01s  | 0.00s   | --    |
| DAA sign       | 2.94s  | 0.01s | :x:    | :x:     | 2.76s   | --    |
| DAA join       | 4.68s  | 1.82s | 2.30s  | 2.30s   | 28.85s  | --    |
| abcdh (irma)   | 8479.76| 9060 | :x: | :x: |  2389.76s* |  2389.76s |

(*) indicates that we had to slightly modify the produced file (roughly by simplifying nested conditionals while preserving their semantics).


We also report on the table below the time needed to find an attack (on well-authentication):
| Protocol    | Time to find an attack in WA |
|:------------|:----------------------------:|
| PACE (faillible dec)                 | 31.81s  |
| PACE (as in [BFK-09](#references))   | 61.43s  |
| PACE                                 | 83.72s  |


## References

[H17]: L. Hirschi.
       PhD Thesis.
       Automated Verification of Privacy in Security Protocols:
       Back and Forth Between Theory & Practice.
       A copy will soon be distributed at http://projects.lsv.ens-cachan.fr/ukano/.

[BFK-09]: J. Bender, M. Fischlin, and D. Kügler.
          Security analysis of the pace key-agreement protocol.
          In Information Security, pages 33–48. Springer, 2009.
	  