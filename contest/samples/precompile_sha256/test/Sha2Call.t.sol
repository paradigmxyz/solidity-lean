// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;
import {Sha2Call} from "../src/Sha2Call.sol";
contract Sha2CallTest {
    function test_digest() public {
        (bool ok, bytes32 d) = new Sha2Call().digest(7);
        require(ok, "ok");
        require(d == sha256(abi.encode(uint256(7))), "digest");
    }
}
