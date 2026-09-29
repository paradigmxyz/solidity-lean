// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;
import "../src/ConditionalFunctionMembers.sol";
contract ConditionalFunctionMembersTest {
    function testMembersBothBranches() public {
        ConditionalFunctionMembers c = new ConditionalFunctionMembers();
        require(c.selectorMatches(true));
        require(c.selectorMatches(false));
        require(c.namedSelectorPure());
    }
}
