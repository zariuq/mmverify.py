This directory contains some examples of the WIP MeTTaMath project to port a MM verifier into MeTTa (and then to foster mathematical reasoning experiments). 

* demo0.mm comes from the Metamath book.
* disjoint2.mm comes from the Metamath github repo tests because a disjoint variable test wsa needed.

The .metta files are the MeTTa commands created post-parsing from the Python mmverify.py file and the calls needed to do verification.

The .log files are the output of running the Python or MeTTa versions.

The following commands were used to generate the examples for disjoint2.mm, demo0.mm, and hol_mini.mm (with file name substitution):

```time python3 mmverify.py -v25 disjoint2.mm --logfile disjoint.log -m disjoint2.metta -r```
```metta disjoint2.metta > metta_disjoint2.log```
