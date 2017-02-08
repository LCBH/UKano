# UKano: UnlinKability and ANOnymity verifier
> - Landing page: http://projects.lsv.ens-cachan.fr/ukano
> - Manual: https://github.com/LCBH/UKano/wiki

*UKano* is a modified version of the [ProVerif](http://proverif.inria.fr)
tool including automatic verification of anonymity and unlinkability of 2-agents protocols.
See the [UKAno webpage](http://projects.lsv.ens-cachan.fr/ukano/) for more details about the tools
and references [HBD16](#links) & [H17](#links) given below for more details on
the underlying theory.

<img align="center" src="http://projects.lsv.ens-cachan.fr/ukano/pictures/International_justice_and_privacy.jpg" width="100" />


## Install

You need OCaml >=3.00 (you can find Objective Caml at http://ocaml.org).
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


## Basic Usage
To run UKano on a protocol written in `filename` (compliant with ProVerif typed format), use
```bash
./ukano <filename>
```
The tool describes the main steps it follows and conlcudes whether unlinkability
and anonymity could be established or not. Type `./ukano --help` to see the list
of options of UKano.


## How it works?
We have proved in [HBD16](#references) and [H17](#references) that, for 2-party protocols,
unlinkability and anonmyity  follow from two sufficent conditions we
called *Frame Opacity* (FO) and *Well-Authentication* (WA). We also show
how to verify those two conditions relying on dedicated encodings.
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

The folder [`./examples/`](./examples) contain some ProVerif files in the expected
format (e.g., [`./examples/Feldhofer/feldhofer.pi`](./examples/Feldhofer/feldhofer.pi)). 
They can be used as a starting point to write your own protocols.


## Links

A complete manual of the tool can be found at https://github.com/LCBH/UKano/wiki. It notably
describes the expected format for input files of UKano.

You can find a comprehensive list of case studies and benchmarks at
https://github.com/LCBH/UKano/blob/master/examples/README.md.

Finally, the underlying theory behind UKano are described in [HBD16] and [H17].


> [HBD16]: L. Hirschi, D. Baelde and S. Delaune.
>      A Method for Verifying Privacy-Type Properties : The Unbounded Case.
>      In IEEE Symposium on Security and Privacy (Oakland), 2016.
>      A copy can be found at http://projects.lsv.ens-cachan.fr/ukano/.
>
> [H17]: L. Hirschi.
>      PhD Thesis.
>	   Automated Verification of Privacy in Security Protocols:
>	   Back and Forth Between Theory & Practice.
>	   A copy will soon be distributed at http://projects.lsv.ens-cachan.fr/ukano/.
