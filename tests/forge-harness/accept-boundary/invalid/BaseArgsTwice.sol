// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// DIV-DUP-INH-MOD #81 reject: base constructor arguments supplied twice — once
// in the inheritance list (`C is B(1)`) and again in the constructor modifier
// list (`constructor() B(2)`). solc rejects: "Base constructor arguments given
// twice."

contract B {
    constructor(uint) {}
}

contract C is B(1) {
    constructor() B(2) {}
}
