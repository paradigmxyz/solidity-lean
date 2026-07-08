// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;
import {CB} from "../src/CB.sol";
interface Vm { function store(address, bytes32, bytes32) external; }
contract CBForgeTest {
    Vm constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    CB private target = new CB();
    function testForgedStorage() public {
        vm.store(address(target), bytes32(uint256(0)), bytes32(uint256(42)));
        require(target.run() == 42, "forged");
    }
}
