// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;
import {CA} from "../src/CA.sol";
interface Vm { function warp(uint256) external; }
contract CAForgeTest {
    Vm constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    CA private target = new CA();
    function testWarp() public {
        vm.warp(12345);
        require(target.ts() == 12345, "warped timestamp");
    }
}
