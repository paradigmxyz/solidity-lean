// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/HighLevelCallOptions.sol";

contract HighLevelCallOptionsForgeTest {
    function testPayKnownPassesValue() public {
        HighLevelCallOptionsTarget target = new HighLevelCallOptionsTarget(99);
        HighLevelCallOptionsCaller caller = new HighLevelCallOptionsCaller();

        uint256 got = caller.payKnown{value: 5}(target, 5);

        require(got == 10, "pay");
    }

    function testReadViewUsesStaticcall() public {
        HighLevelCallOptionsTarget target = new HighLevelCallOptionsTarget(99);
        HighLevelCallOptionsCaller caller = new HighLevelCallOptionsCaller();

        uint256 got = caller.readView(target);

        require(got == 99, "view");
    }
}
