// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

import "../src/TupleLiteralTargetTyping.sol";

contract TupleLiteralTargetTypingTest {
    function testTupleLiteralTargetTyping() public {
        TupleLiteralTargetTyping c = new TupleLiteralTargetTyping();
        (bytes4 hexValue, uint256 one) = c.hexDeclaration();
        require(hexValue == 0x11223344 && one == 1);
        (bytes4 stringValue, uint256 two) = c.stringDeclaration();
        require(stringValue == 0x61626364 && two == 2);
        (bytes4 assigned, uint256 three) = c.hexAssignment();
        require(assigned == 0x11223344 && three == 3);
    }
}
