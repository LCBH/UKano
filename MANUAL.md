# Manual of UKano v0.3
> Lucca Hirschi
> http://projects.lsv.ens-cachan.fr/ukano/

*UKano* is a modified version of the [ProVerif](http://proverif.inria.fr)
tool including automatic verification of anonymity and unlinkability of 2-agents protocols.
See references [HBD17](#references) & [HBD16](#references) given below for more details on
the underlying theory.

<img align="center" 
src="http://projects.lsv.ens-cachan.fr/ukano/pictures/International_justice_and_privacy.jpg" 
width="100" />


## Install

You need OCaml >=3.00 (you can find Objective Caml at http://ocaml.org).
Just type: `make`.
The executable program `ukano` and `proverif` have been built.

You can also build UKano only by typing `make ukano`. UKano needs an exectuable of ProVerif though.
We recommend using the version shipped with UKano but one can specify the path some ProVerif executable
with the option `--proverif <path>`. *Warning*: if one wants to use its own ProVerif executable, then one
needs a version '>1.97' patched with the 'biproj.patch' in 'proverif1.97' folder of the repository,


## Quick Test

To quickly test the tool on our case studies: build it, choose an example
in the examples folder (e.g., 
[`./examples/Feldhofer/feldhofer.pi`](./examples/Feldhofer/feldhofer.pi))
and type `./ukano <path-example>`.

To test the tool against examples with known expected conclusions, you can also type `make test`.

## Usage

### Basic
To run UKano on a protocol written in `filename` (compliant with ProVerif typed format, see [Section 
Expected Format](#expected-format) for more details of this format), use 
```bash
./ukano <filename>
```
The tool describes the main steps it follows and concludes whether unlinkability
and anonymity could be established or not.


### How it works?
We have proved in [HBD17](#references) (preliminary versions in [HBD16](#references) and [H17](#references))
that, for 2-party protocols, unlinkability and anonmyity follow from two sufficent conditions we
called *Frame Opacity* (FO) and *Well-Authentication* (WA). We also show how to verify those two
conditions relying on dedicated encodings.
UKAno mechanizes all those encodings.

After parsing your file, the tool creates two other files in the same
directory. Each file encodes one of our two sufficient conditions. 
The one encoding FO is suffixed with `_FOpa.pi`. The second suffixed
with `_WAuth.pi` can be used to check WA. The latter contains a query
per conditional.
UKano then launches `proverif` on those two files and parse the results
in order to conclude whether both conditions have been established. In such
a case, the tool concludes that the input protocol ensures unlinkability and
anonymity.

The folder [`./examples/`](./examples) contains some ProVerif files in the expected
format (e.g., [`./examples/Feldhofer/feldhofer.pi`](./examples/Feldhofer/feldhofer.pi)). 
They can be used as a starting point to write your own protocols.


### Options
Here are the options you may use:
```bash
$ ./ukano --help
UKano v0.2 : Cryptographic privacy verifier, by Lucca Hirschi. Based on Proverif v1.91, by Bruno 
Blanchet and Vincent Cheval.
  --proverif            path of the ProVerif executable to use (optional, default: './proverif')
  --ideal-no-check      assume the idealisation is conform (requires manual checks)
  --ideal-automatic     do not take given idealisations into account, generate them automatically 
instead (using the default quasi-syntaxic heuristic)
  --ideal-semantic      modifies the idealisation heuristic: put fresh names for all non-tuple 
sub-terms
  --ideal-syntaxic      modifies the idealisation heuristic: go through all functions (including 
ones in equations) and replace identity names and let variables by holes. Conformity checks are 
modified accordingly.
  --only-fo             verifies the frame opacity condition only
  --only-wa             verifies the well-authentication condition only
  --fo-with-let         verifies the frame opacity condition using old encodings based on nested 'let' constructs 
  --clean               remove generated files after successful verification
  --less-verbose        reduce the verbosity
  --log-proverif        log in stdout all ProVerif outputs
  -gc                   display gc statistics
```

Some options are described in the next section.

### Idealisations Heuristics
We now describe the heuristic UKano uses by default to guess idealisations automatically (corresponding
to the *quasi-syntaxic heuristic* from [HBD17](#references)).
Given a syntactic output `u` in some role, we recursively build an idealisation by case analysis on 
`u`:
 1. a constant, we let `u` be its idealisation
 2. a session name, we let `u` be its idealisation
 3. a name that is not a session name, we let a new session name be its idealisation (but two 
occurrences of the same name will be idealised with the same session name) 
 4. a variable bind by an input, we let `u` be its idealisation
 5. variable bind by a let, we let a fresh session name be its idealisation (but two occurrences of 
the same variable will be idealised with the same session name) 
 6. `u=f(u1,...,un)`, `vi` are idealisations of `ui` and `f` does not occur in equations then we let 
`f(v1,...,vn)` be the idealisation of `u`
 7. `u=f(u1,...,un)` and `f` does occur in equations then we let a fresh session name be the 
idealisation of `u`

The options `--ideal-semantic` and `--ideal-syntaxic` allow to modify the above heuristic:
 - `--ideal-semantic` replaces the cases 6. and 7. as follows: when `f` is not a tuple then the 
idealisation is a fresh session name, otherwise we proceed as in 6.
 - `--ideal-syntaxic` removes the case 7 and removes the condition "`f` does not occur in 
equations " in case 6. In case the protocol is in the shared case, UKano then displays a warning 
message saying that the user should verify WA item (ii) separately.

UKano checks the conformity of guessed idealisations as well as idealisations given by the user. 
Those checks can be bypassed using the option `--ideal-no-check`.

The option `--ideal-automatic` makes UKano bypass idealisations given in input files and 
automatically guess idealisations instead.


### Expected Format
Only typed ProVerif files are accepted (proverif should successfully parse
it when using the option `-in pitype`). Please refer to the manual of ProVerif
on the [Proverif webpage](http://proverif.inria.fr). Additionally, the file should
not define new types and only use types `bitstring` and `channel`. The file must
declare at least one channel `c` (i.e., contains a line `free c:channel.`).

After the definition of the equational theory (without any declaration of
events), the inputted file should contain a commentary:
```bash
       (* ==PROTOCOL== *)
```
and then define only one process corresponding to the whole multiple
sessions system. This process should satisfy the syntactical
restrictions described in [HBD17](#references). However, multiple tests (conditional or
evaluation) can be performed in a row between an input and an output
if the corresponding `else` branches are the same. You can also use most
of syntactical sugars allowed by ProVerif (e.g., modular definitions
through definitions of functions and call, etc.).
Finally, to check anonymity as well, identity names to be revealed
(and only them) must have `id` as prefix (e.g., `idName`). 

#### Improve Precision
Note that, currently, UKano does not detect safe conditionals and consider
all conditionals unsafe by default. UKano lists conditionals for which WA
could not be established. You should check that they correspond to safe
conditionals.

If the tool cannot guess idealisations of outputs (to check frame opacity),
you can play with the options described in [Section Idealisations 
Heuristics](#idealisations-heuristics)
or compute them manually and add it to the file as explained next.

Output messages that cannot be guessed automatically should be of the form:
`choice[u,uh]` where `u` is the real message outputted by the protocol and
`uh` is the idealised message.
If you define in the equational theory a constant `hole` (by adding this
line: `free hole:bitstring.`) then all `hole` will be replaced by fresh
and pairwise distinct session names.

Finally, when frame opacity cannot be checked directly, it is sometimes
possible to make ProVerif prove it just by slightly modifying the file
without altering the underlying protocol (for instance, by moving creation
of names).


## Our Case Studies
We list all our case studies in the [next section](#list-of-case-studies) and provide
benchmarks in section [Benchmarks](#benchmarks).

Finally, note that for some protocols, specific idealisations
heuristics are needed as explained in the [dedicated section](#idealisations-heuristics).
We also list in section [Benchmarks](#benchmarks) the different results
(conclusion and time needed to conclude) one obtains depending on the chosen heuristic.


### List of Case Studies
See the table below. References to the protocols can be found in [HBD17] and models that can be fed 
to UKano can be found in the folder 
[`./examples`](https://github.com/LCBH/UKano/tree/master/examples).

Legend:
- :white_check_mark: : means that the corresponding condition or property could be automaticaly 
established using UKano
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


### Benchmarks
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
- "default" corresponds to the default heuristic of UKano (quasi-syntaxic in [HBD17])
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
| DAA simplified [HBD17]| 0.02s | 0.01s | :x:| 0.01s | 0.01s   | --    |
| DAA sign       | 3.77s  | 0.03s | :x:    | :x:     | :x:     | 3.74s |
| DAA join       | 31.81s | 29.57s*  | :x: | 1.24s   | 2.29s   | 1.79s |
| abcdh (irma)   | 9072.75s |  9060s* | :x:| :x:     | 38.20s  | 12.75s|

(*) indicates that we had to slightly modify the produced file, refer to [HBD17](#references) for more details.

We also report on the table below the time needed to find an attack (on well-authentication):

| Protocol    | Time to find an attack in WA |
|:------------|:----------------------------:|
| PACE (faillible dec)                 | 31.81s  |
| PACE (as in [BFK-09](#references))   | 61.43s  |
| PACE                                 | 83.72s  |


#### Out-of-date benchmarks using old encoding for proving FO (to remove before release of v0.3)
(DAA case studies were flawed and are now fixed, this also explain differences with the previous table)

| Protocol    | Best time (total) | Time for WA | Time for FO (semantic) | Time for FO (default) | Time for FO (syntaxic)  | Time for FO (user-defined) |
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
| abcdh (irma)   | 8479.76| 9060* | :x: | :x: |  2389.76s* |  2389.76s |


## References
[HBD17]: L. Hirschi, D. Baelde and S. Delaune.
	A method for unbounded verification of privacy-type properties (journal).
    A copy is available at http://www.lsv.fr/~hirschi/pdfs/UK_journal.pdf.

[H17]: L. Hirschi.
    PhD Thesis.
    Automated Verification of Privacy in Security Protocols:
    Back and Forth Between Theory & Practice.
    A copy is available at http://www.lsv.fr/~hirschi/defense.php.

[HBD16]: L. Hirschi, D. Baelde and S. Delaune.
     A Method for Verifying Privacy-Type Properties : The Unbounded Case.
     In IEEE Symposium on Security and Privacy (Oakland), 2016. To appear.
     A copy can be found at http://projects.lsv.ens-cachan.fr/ukano/.

[BFK-09]: J. Bender, M. Fischlin, and D. Kügler.
    Security analysis of the pace key-agreement protocol.
    In Information Security, pages 33–48. Springer, 2009.
