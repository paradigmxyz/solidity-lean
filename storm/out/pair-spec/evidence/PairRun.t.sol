// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;
import "forge-std/Test.sol";

contract Tok {
    mapping(address => uint256) public balanceOf;
    function mint(address a, uint256 v) external { balanceOf[a] += v; }
    function transfer(address to, uint256 v) external returns (bool) {
        balanceOf[msg.sender] -= v; balanceOf[to] += v; return true;
    }
}

contract PairRun is Test {
    address constant PAIR = address(0x1000);
    address constant TO = address(0x3000);

    function setUpPair(bytes memory code, address t0, address t1) internal {
        vm.etch(PAIR, code);
        vm.store(PAIR, bytes32(uint256(6)), bytes32(uint256(uint160(t0))));
        vm.store(PAIR, bytes32(uint256(7)), bytes32(uint256(uint160(t1))));
        // reserves 10000 / 10000, blockTimestampLast 0
        vm.store(PAIR, bytes32(uint256(8)), bytes32(uint256(10000) | (uint256(10000) << 112)));
        vm.store(PAIR, bytes32(uint256(12)), bytes32(uint256(1)));
    }

    function reserves() internal view returns (uint256 r0, uint256 r1) {
        uint256 w = uint256(vm.load(PAIR, bytes32(uint256(8))));
        r0 = w & ((1 << 112) - 1);
        r1 = (w >> 112) & ((1 << 112) - 1);
    }

    function run1(string memory hexfile) internal returns (bool ok, uint256 r0, uint256 r1) {
        Tok a = new Tok(); Tok b = new Tok();
        setUpPair(vm.parseBytes(vm.readFile(hexfile)), address(a), address(b));
        a.mint(PAIR, 11000); // 10000 reserve + 1000 in
        b.mint(PAIR, 10000);
        (ok,) = PAIR.call(abi.encodeWithSignature("swap(uint256,uint256,address,bytes)", 0, 906, TO, ""));
        (r0, r1) = reserves();
    }

    function test_swap_real() public {
        (bool ok, uint256 r0, uint256 r1) = run1("pair.hex");
        emit log_named_uint("ok", ok ? 1 : 0); emit log_named_uint("r0", r0); emit log_named_uint("r1", r1);
        assertTrue(ok); assertEq(r0, 11000); assertEq(r1, 9094);
    }

    function test_swap_906_plus_one_reverts() public {
        Tok a = new Tok(); Tok b = new Tok();
        setUpPair(vm.parseBytes(vm.readFile("pair.hex")), address(a), address(b));
        a.mint(PAIR, 11000); b.mint(PAIR, 10000);
        (bool ok,) = PAIR.call(abi.encodeWithSignature("swap(uint256,uint256,address,bytes)", 0, 907, TO, ""));
        assertFalse(ok);
    }

    function test_swap_noupdate_mutant() public {
        (bool ok, uint256 r0, uint256 r1) = run1("pair-noupdate.hex");
        emit log_named_uint("ok", ok ? 1 : 0); emit log_named_uint("r0", r0); emit log_named_uint("r1", r1);
        assertTrue(ok); assertEq(r0, 10000); assertEq(r1, 10000);
    }

    function test_closed_world_reverts() public {
        // tokens without code, as in Target.preState: every swap, skim and sync reverts
        setUpPair(vm.parseBytes(vm.readFile("pair.hex")), address(0x4000), address(0x5000));
        (bool ok1,) = PAIR.call(abi.encodeWithSignature("swap(uint256,uint256,address,bytes)", 0, 906, TO, ""));
        (bool ok2,) = PAIR.call(abi.encodeWithSignature("skim(address)", TO));
        (bool ok3,) = PAIR.call(abi.encodeWithSignature("sync()"));
        assertFalse(ok1); assertFalse(ok2); assertFalse(ok3);
    }
}

