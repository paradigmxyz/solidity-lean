// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

function headerFreeArg() view returns (uint256) {
    return block.number + 7;
}

function headerTwice(uint256 value) pure returns (uint256) {
    return value * 2;
}

library HeaderMath {
    function plusOne(uint256 value) internal pure returns (uint256) {
        return value + 1;
    }
}

library ContractHeaderMath {
    function timesThree(uint256 value) internal pure returns (uint256) {
        return value * 3;
    }
}

interface HeaderOracle {
    function seed() external view returns (uint256);
}

HeaderOracle constant HEADER_ORACLE = HeaderOracle(address(0xbeef));

using {headerTwice} for uint256;
using HeaderMath for uint256;

contract RuntimeArgBase {
    uint256 public seed;

    constructor(uint256 value) {
        seed = value;
    }
}

contract BlockArg is RuntimeArgBase(block.number + 1) {}

contract SenderArg is RuntimeArgBase(uint160(msg.sender)) {}

contract ValueArg is RuntimeArgBase(msg.value + 3) {
    constructor() payable {}
}

contract NonpayableValueArg is RuntimeArgBase(msg.value + 4) {}

contract FreeCallArg is RuntimeArgBase(headerFreeArg()) {}

contract FreeUsingArg is RuntimeArgBase(uint256(3).headerTwice()) {}

contract LibraryUsingArg is RuntimeArgBase(uint256(4).plusOne()) {}

contract ContractUsingArg is RuntimeArgBase(uint256(5).timesThree()) {
    using ContractHeaderMath for uint256;
}

contract ExternalCallArg is RuntimeArgBase(HEADER_ORACLE.seed()) {}

contract ThisCallArg is RuntimeArgBase(this.seedSource()) {
    function seedSource() external pure returns (uint256) {
        return 13;
    }
}

contract ModifierParamArg is RuntimeArgBase {
    constructor(uint256 value) RuntimeArgBase(value + 1) {}
}

contract BalanceArg is RuntimeArgBase(address(this).balance) {
    constructor() payable {}
}
