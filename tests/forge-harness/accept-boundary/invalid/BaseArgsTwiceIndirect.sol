// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// DIV-DUP-INH-MOD #81 reject (indirect): A's constructor arguments are supplied
// by B's inheritance list (`B is A(1)`) AND re-supplied by C's constructor
// modifier (`constructor() A(2)`). The inheritance-supplied set spans the whole
// linearization, not just the direct base. solc rejects: "Base constructor
// arguments given twice."

contract A {
    constructor(uint) {}
}

contract B is A(1) {}

contract C is B {
    constructor() A(2) {}
}
