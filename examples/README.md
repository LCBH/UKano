# Our Case Studies
We have tested UKano on several real-world case studies.
This folder contains all ProVerif models for which unlinkability
and anonymity can be automatically established using UKano.
They all have a dedicatd folder in [`./examples/`](.).


We list them all in the [next section](#list-of-case-studies) and provide
benchmarks in section [Benchmarks](#benchmarks).

Finally, note that for some protocols, you need to use specific idealisation
heuristics as explained in the [dedicated section of the wiki](https://github.com/LCBH/UKano/wiki#idealisations-heuristics).
We also list in section [Benchmarks](#benchmarks) the different results
(conclusion and time needed to conclude) one obtains depending on the chosen heuristic.

Remark that, in some files, we may use multiple conditionals in a row to ease the readability.
Note that UKano considers them as a single compacted conditional. We also show how
UKano detects some attacks on variations of protocols that do not satisfy our conditions
(corresponding files end with `-attack.pi`).

Finally, the folder [`./examples/tamarin/`](./tamarin/) contains
some Tamarin models mentioned in [H17] and in [HBD19]; they are obviously not valid
UKano files.

## List of Case Studies
See the table below. References to the protocols can be found at [HBD17].

Legend:
- :heavy_check_mark: : means that the corresponding condition or property could be automaticaly established using UKano
- :x: : when a condition fails to hold or could not be established
- :fire: : when an attack has been found

| Protocol | Frame-Opacity | Well-Authentication | Unlinkability |
|:---------|:-------------:|:-------------------:|:-------------:|
| Hash-Lock | :heavy_check_mark: | :heavy_check_mark: | :heavy_check_mark: |
| LAK (stateless) | --  | :x: | :fire: |
| Fixed LAK | :heavy_check_mark: | :heavy_check_mark: | :heavy_check_mark: |
| BAC       | :heavy_check_mark: | :heavy_check_mark: | :heavy_check_mark: |
| BAC+ PA+ AA | :heavy_check_mark: | :heavy_check_mark: | :heavy_check_mark: |
| BAC+ AA+ PA | :heavy_check_mark: | :heavy_check_mark: | :heavy_check_mark: |
| PACE (faillible dec) |  -- | :x: | :fire: |
| PACE (as in~[BFK-09](#references))     |  -- | :x: | :fire: |
| PACE | -- | :x: | :fire: |
| PACE with tags | :heavy_check_mark: | :heavy_check_mark: | :heavy_check_mark: |
| DAA sign | :heavy_check_mark: | :heavy_check_mark: | :heavy_check_mark: |
| DAA sign (shared, as in Ex11 in [HBD19]) | :x: | :heavy_check_mark: | :fire: |
| DAA join | :heavy_check_mark: | :heavy_check_mark: | :heavy_check_mark: |
| abcdh (irma) | :heavy_check_mark: | :heavy_check_mark: | :heavy_check_mark: |


## Benchmarks (outdated)
All benchmarks are performed using UKano v0.3 (with ProVerif v1.97 as backend)
without user-defined idealisations (except for some cases indicated with (*)).
For most cases, the verification is thus truly fully automatic.

Here are the specs of the machine we used:
- OS: Linux sume 3.10-2-amd64 #1 SMP Debian 3.10.5-1 (2013-08-07) x86_64 GNU/Linux
- CPU: Intel(R) Xeon(R) CPU X5650 @ 2.67GHz / stepping: 2 / microcode: 0x13 / cpu MHz: 2659.937 / 
cache size: 12288 KB
- RAM: 47GO
	    
Legend: time in seconds when verification was successful, :x: when condition
could not be established, :curly_loop: when the verification took too much time (>20 hours) or too
much memory (>20GO of RAM), and, -- when it was not necessary to build idealisations manually
(i.e., user defined). The different columns for FO (i.e., frame opacity) refers to the different
heuristics implemented in  UKano to build idealisations:
- "semantic" corresponds to the option `--ideal-semantic`
- "default" corresponds to the default heuristic of UKano (quasi-syntaxic in [HBD19])
- "syntaxic" corresponds to the option `--ideal-syntaxic`
- "user-defined" when a user-defined idealisation was given to the tool.

| Protocol    | Best time (total) | Time for WA | Time for FO (semantic) | Time for FO (default) | Time for FO (syntaxic)  | Time for FO (user-defined) |
|:------------|:-------------:|:-------------------:|:-------------------:|:---------------------:|:--------------------:|:---------------------------|
| Hash-Lock      | 0.00s  | 0.00s | 0.00s  | 0.00s   | 0.00s   | --    |
| Fixed LAK      | 0.00s  | 0.00s | 0.00s  | 0.00s   | 0.00s   | --    |
| BAC            | 0.03s  | 0.02s | 0.01s  | 0.04s   | 0.04s   | --    |
| BAC+AA+PA      | 0.46s  | 0.42s | 0.04s  | 0.22s   | 0.22s   | --    |
| BAC+PA+AA      | 0.40s  | 0.36s | 0.04s  | 0.52s   | 0.50s   | --    |
| PACE with tags | 78.40s | 72.40s| 6.00s  | 6.19s   | 16.44s  | --    |
| DAA simplified [HBD19]| 0.02s | 0.01s | :x:| 0.01s | 0.01s   | --    |
| DAA sign       | 3.77s  | 0.03s | :x:    | :x:     | :x:     | 3.74s |
| DAA join       | 31.81s | 29.57s*  | :x: | 1.24s   | 2.29s   | 1.79s |
| abcdh (irma)   | 9072.75s |  9060s* | :x:| :x:     | 38.20s  | 12.75s|

(*) indicates that we had to slightly modify the produced file, refer to [HBD19](#references) for more details.

We also report on the table below the time needed to find an attack (on well-au\thentication):

| Protocol    | Time to find an attack in WA |
|:------------|:----------------------------:|
| PACE (faillible dec)                 | 31.81s  |
| PACE (as in [BFK-09](#references))   | 61.43s  |
| PACE                                 | 83.72s  |


## References
[HBD19]: L. Hirschi, D. Baelde, S. Delaune.
    A method for unbounded verication of privacy-type properties.
    Will appear in the [Journal of Computer Security](https://www.iospress.nl/journal/journal-of-computer-security/).
    A copy can be found on [ARXIV](https://arxiv.org/pdf/1710.02049.pdf).

[H17]: L. Hirschi.
    PhD Thesis.
    Automated Verification of Privacy in Security Protocols:
    Back and Forth Between Theory & Practice.
    A copy can be found at on [HAL](https://tel.archives-ouvertes.fr/tel-01534145/document).

[BFK-09]: J. Bender, M. Fischlin, and D. Kügler.
    Security analysis of the pace key-agreement protocol.
    In Information Security, pages 33–48. Springer, 2009.
	  
