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
	    
Legend: time in seconds when verification was successful, :x: when condition
could not be established, :curly_loop: when the verification took too much time (>2 hours) or too
much memory (>10GO of RAM), and, -- when it was not necessary to build idealizations manually
(i.e., user defined). The different columns for FO (i.e., frame opacity) refers to the different
heuristics of UKano to build idealization:
- "greedy" corresponds to the option `--idea-greedy`
- "default" corresponds to the default heuristics of UKano
- "syntax" corresponds to the option `--idea-full-syntax`
- "user-defined" when a user defined idealization is necessary


| Protocol    | Better time (total) | Time for WA | Time for FO (greedy) | Time for FO (default) | Time for FO (syntax)  | Time for FO (user-defined) |
|:------------|:-------------:|:-------------------:|:-------------------:|:---------------------:|:--------------------:|:---------------------------|
| Hash-Lock      | 0.03s  | 0.01s | 0.02s  | 0.02s   | 0.02s   | --    |
| Fixed LAK      | 0.03s  | 0.01s | 0.02s  | 0.02s   | 0.02s   | --    |
| BAC            | 70.65s | 0.09s | 66.56s | 128.03s | 132.24s | --    |
| BAC+AA+PA      |1290.46s| 2.11s | 1288.46s| :curly_loop: | :curly_loop: | --    |
| BAC+PA+AA      | 70.65s | 1.86s |1151.84s| :curly_loop: | :curly_loop: | --    |
| PACE with tags | todo   |491.16s|        |         |         |       |
| DAA simplified [HBD17]| 0.12s |0.02s|0.10s| 0.10s  | 0.10s   | --    |
| DAA sign       | 89.24s | 0.08s | :x:    | :x:     | 89.16s  | --    |
| DAA join       | 21.84s | 0.01s | 21.83s | 22.25s  | 60.07s  | --    |
| abcdh (irma)   | todo   |       |        |         |         |       |

[//]: # (BAC+AA+PA: default: 6111.04s | syntax: 6017.32s)
[//]: # (BAC+PA+AA: default: 7134.94s | syntax: )
[//]: # (TODO: solve problems with abcdh and termination with pace)


## References
[HBD17]: L. Hirschi, D. Baelde and S. Delaune.
     A Method for Verifying Privacy-Type Properties : The Unbounded Case.
     Journal version under submission.
     A copy will soon be available at http://projects.lsv.ens-cachan.fr/ukano/.
