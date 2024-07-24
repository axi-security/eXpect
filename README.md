# eXpect: On The Security Implications of AXI Implementations Violations

This repository contains the properties that eXpect defines. The properties are written as System Verilog Assertions(SVAs). 
The properties serve to exhaustively and systematically test AXI implementations. This model represents a best-effort formal approach.
They are numbered as presented in the paper. 


## Property Files
We provide the following property files to verify AXI implementations:
- _assert\_axi4lite\_sub.sv_: AXI4-Lite Subordinate.
- _assert\_axi4lite\_man.sv_: AXI4-Lite Manager
- _assert\_axi4full\_sub.sv_: AXI4 Subordinate
- _assert\_axi4full\_man.sv_: AXI4 Manager

The AXI4 properties include the burst mode modeling in addition to the AXI4-Lite properties. 
Depending on the tested implementation, whether it is a manager or a subordinate, or if it's the LITE or FULL version of the protocol, 
the corresponding property file can be associated.


## USE
This repository only contains the property files. They have to be embedded into the QuestaFormal tool.
We ran both QuestaCDCFormal 2021 and QuestaCDCFormal 2022 on Ubuntu 20.4. The tool is not freely available.
https://eda.sw.siemens.com/en-US/ic/questa/formal-verification/property-checking/
