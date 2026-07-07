// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract A {
    uint256 public log;
    constructor() { log = log * 10 + 1; }
    function who() public virtual returns (uint256) { return 1; }
}
contract B is A {
    constructor() { log = log * 10 + 2; }
    function who() public virtual override returns (uint256) { return 2; }
}
contract C is A {
    constructor() { log = log * 10 + 3; }
    function who() public virtual override returns (uint256) { return 3; }
}
contract D is B, C {
    constructor() { log = log * 10 + 4; }
    function who() public override(B, C) returns (uint256) { return super.who(); }
    function getLog() external view returns (uint256) { return log; }
}
