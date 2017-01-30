# UKano: UnlinKability and ANOnymity verifier
> - Land page: http://projects.lsv.ens-cachan.fr/ukano
> - Wiki: https://github.com/LCBH/UKano/wiki

*UKano* is a modified version of the [ProVerif](http://proverif.inria.fr)
tool including automatic verification of anonymity and unlinkability of 2-agents protocols.
See [UKAno webpage](http://projects.lsv.ens-cachan.fr/ukano/) and the paper [HBD16](#references)
for more details and the underlying theory.

<img align="center" src="http://projects.lsv.ens-cachan.fr/ukano/pictures/International_justice_and_privacy.jpg" width="100" />


## Install

You need OCaml >=3.00 (you can find Objective Caml at [OCaml webpage](ocaml.org)).
Just type: `make`.
The executable program `ukano` and `proverif` have been built.

You can also build UKano only by typing `make ukano`.
UKano needs an exectuable of ProVerif though. You can specify the path of
your ProVerif executable with the option `--proverif <path>`.


## Quick Test

To quickly test the tool on our case studies: build it, choose an example
in the examples folder (e.g., [`./examples/Feldhofer/feldhofer.pi`](./examples/Feldhofer/feldhofer.pi))
and type `./ukano <path-example>`.

To test the tool against examples with known expected conclusions, you can also type `make test`.

## Usage

### Basic
To run UKano on a protocol written in `filename` (compliant with ProVerif typed format, see [Section Expected Format](#expected-format) for more details), use 
```bash
./ukano <filename>
```
The tool describes the main steps it follows and conlcudes whether unlinkability
and anonymity could be established or not.


### How it works?
We have proved in [HBD16](#references) that, for 2-party protocols,
unlinkability and anonmyity  follow from two sufficent conditions we
called *Frame Opacity* (FO) and *Well-Authentication* (WA). We also show
how to verify those two conditions relying on dedicated encodings.
UKAno mechanizes all those encodings.

After parsing your file, the tool creates two other files in the same
directory. Each file encodes one of our two sufficient conditions. 
The one encoding FO is suffixed with `_FOpa.pi`. The second suffixed
with `_WAuth.pi` can be used to check WA. The latter contains a query
per conditional.
UKano then launches `proverif` on those two models and parse the results
in order to conclue whether both conditions have been established. In such
a case, the tool concludes that the input protocol ensures unlinkability and
anonymity.

The folder [`./examples/`](./examples) contain some ProVerif files in the expected
format (e.g., [`./examples/Feldhofer/feldhofer.pi`](./examples/Feldhofer/feldhofer.pi)). 
They can be used as a starting point to write your own protocols.


### Options
Here are the options you may use:
```bash
$ ./ukano --help
UKano 0.1. Cryptographic privacy verifier, by Lucca Hirschi. Based on Proverif 1.91, by Bruno Blanchet and Vincent Cheval.
  --proverif            path of the ProVerif executable to use (optional, default: './proverif')
  --idea-no-check       assume the idealization is conform (requires manual checks)
  --idea-automatic      do not takes given diealizations into account, generate them automatically instead
  --idea-greedy         modifies the idealization heuristics: put fresh names for all non-tuple sub-terms
  --idea-full-syntax    modifies the idealization heuristics: go through all functions (including ones in equations) and replace identity names and let variables by holes
  --only-fo             verifies the frame opacity condition only
  --only-wa             verifies the well-authentication condition only
  --clean               remove generated files after successful verification
  --less-verbose        reduce the verbosity
  -gc                   display gc statistics (optional)
```

Some options are described in the next section.

### Idealizations Heuristics
By default, the heuristics UKano uses to guess idealizations works as follows.
Given a syntactic output `u` in some role, we recursively build an idealization by case analysis on `u`:
 1. a constant, we let `u` be its idealization
 2. a session name, we let `u` be its idealization
 3. a name that is not a session name, we let a fresh session name be its idealization 
 4. a variable bind by an input, we let `u` be its idealization
 5. variable bind by a let, we let a fresh session name be its idealization 
 6. `u=f(u1,...,un)`, `vi` are idealizations of `ui` and `f` does not occur in equations then we let `f(v1,...,vn)` be the idealization of `u`
 7. `u=f(u1,...,un)` and `f` does occur in equations then we let a fresh session name be the idealization of `u`

The options `--idea-greedy` and `--idea-full-syntax` allows to modify the above heuristics:
 - `--idea-greedy` replaces the cases 6. and 7. as follows: when `f` is not a tuple then the idealization is a fresh session name, otherwise we proceed as in 6.
 - `--idea-full-syntax` removes the case 7 and removes the condition "`f` does not occur in equations " in case 6. In case the protocol is in the shared case, UKano then displays a warning message saying that the user should verifies WA item (ii) separately.

UKano checks the confomity of guessed idealizations as well as idealizations given by the user. Those checks can be bypassed using the option `--idea-no-check`.

The option `--idea-automatic` makes UKano bypass idealizations given in input files and automatically guess idealizations instead.


### Expected Format
Only typed ProVerif files are accepted (ProVerif should successfully parse
it when using the option `-in pitype`). Please refer to the manual of ProVerif
at [ProVerif webpage](http://proverif.inria.fr). Additionally, the file should
not define new types and only use types `bitstring` and `channel`. The file must
declare at least one channel `c` (i.e., contains a line `free c:channel.`).

After the definition of the equational theory (without any declaration of
events), the inputted file should contain a commentary:
```bash
       (* ==PROTOCOL== *)
```
and then define only one process corresponding to the whole multiple
sessions system. This process should satisfy the syntactical
restrictions described in [1]. However, multiple tests (conditional or
evaluation) can be performed in a row between an input and an output
if the corresponding `else` branches are the same. You can also use most
of syntactical sugars allowed by ProVerif (e.g., modular definitions
through definitions of functions and call, etc.).
Finally, to check anonymity as well, identity names to be revealed
(and only them) must have `id` as prefix (e.g., `idName`). 


#### Improve precision
Note that, currently, UKano does not detect safe conditionals and consider
all conditionals unsafe by default. UKano lists conditionals for which WA
could not be established. You should check that they correspond to safe
conditionals.

If the tool cannot guess idealizations of outputs (to check frame opacity),
you can play with the options described in [Sectionc Idealizations Heuristics](#idealizations-heuristics)
or compute them manually and add it to the file as explained next.

First, the equational theory must declare a constant `hole` by adding this
line: `free hole:bitstring.`. Output messages that cannot be guessed
automatically should be of the form: `choice[u,uh]` where `u` is the real
message outputted by the protocol and `uh` is the idealization of any concrete
message outputted here (by using the constant `hole`). All `hole` will be replaced
by a fresh session name.

Finally, when frame opacity cannot be checked directly, it is sometimes
possible to make ProVerif prove it just by slightly modifying the file
without altering the underlying protocol (for instance, by moving creation
of names).


## Our Case Studies
We have tested UKano on several real-world case studies.
We list them all below. They all have a dedicatd folder in [`./examples/`](./examples).

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
| BAC+ PA AA | :white_check_mark: | :white_check_mark: | :white_check_mark: |
| PACE (faillible dec) |  -- | :x: | :fire: |
| PACE (as in~[BFK-09](#references))     |  -- | :x: | :fire: |
| PACE | -- | :x: | :fire: |
| PACE with tags | :white_check_mark: | :white_check_mark: | :white_check_mark: |
| DAA sign | :white_check_mark: | :white_check_mark: | :white_check_mark: |
| DAA join | :white_check_mark: | :white_check_mark: | :white_check_mark: |
| abcdh (irma) | :white_check_mark: | :white_check_mark: | :white_check_mark: |


## References
[HBD16]: L. Hirschi, D. Baelde and S. Delaune.
     A Method for Verifying Privacy-Type Properties : The Unbounded Case.
     In IEEE Symposium on Security and Privacy (Oakland), 2016. To appear.
     A copy can be found at http://projects.lsv.ens-cachan.fr/ukano/.

[BFK-09]: J. Bender, M. Fischlin, and D. Kügler.
     Security analysis of the pace key-agreement protocol.
     In Information Security, pages 33–48. Springer, 2009.
