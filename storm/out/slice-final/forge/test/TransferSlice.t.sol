// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;
import {Test, Vm} from "forge-std/Test.sol";

/// Executes the exact runtime bytes solar emitted for UniswapV2ERC20 (scope: transfer only) and checks
/// the sequential transfer post of docs/CERTIFICATION_TARGET.md on concrete and fuzzed calls, from
/// arbitrary callers. Mutated bytes must fail the same checks (negative controls by execution).
contract TransferSlice is Test {
    bytes32 constant TOPIC = 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef;
    address constant T = address(0x1000);

    function code() internal view returns (bytes memory) {
        return vm.parseBytes(vm.readFile(vm.envString("RUNTIME_HEX")));
    }

    function slot(address a) internal pure returns (bytes32) { return keccak256(abi.encode(a, uint256(1))); }
    function bal(address a) internal view returns (uint256) { return uint256(vm.load(T, slot(a))); }

    function errData(string memory m) internal pure returns (bytes memory) {
        return abi.encodeWithSignature("Error(string)", m);
    }

    /// The post: returns "" when the observed run meets it, else the reason.
    function post(bytes memory c, address caller, address to, uint256 b0, uint256 bt, uint256 v)
        internal returns (string memory)
    {
        vm.etch(T, c);
        vm.store(T, slot(caller), bytes32(b0));
        if (caller != to) vm.store(T, slot(to), bytes32(bt));
        uint256 btEff = caller == to ? b0 : bt;
        vm.recordLogs();
        vm.prank(caller);
        (bool ok, bytes memory out) = T.call(abi.encodeWithSelector(0xa9059cbb, to, v));
        Vm.Log[] memory logs = vm.getRecordedLogs();
        // Sequential: debit the caller, then credit the recipient reading the debited state.
        bool debitOk = v <= b0;
        uint256 afterDebitTo = caller == to ? b0 - (debitOk ? v : 0) : bt;
        bool succeeds = debitOk && (caller == to || bt <= type(uint256).max - v);
        if (succeeds) {
            if (!ok) return "reverted on a call the post says succeeds";
            if (keccak256(out) != keccak256(abi.encode(true))) return "wrong return data";
            if (logs.length != 1 || logs[0].topics.length != 3 || logs[0].topics[0] != TOPIC
                || logs[0].topics[1] != bytes32(uint256(uint160(caller)))
                || logs[0].topics[2] != bytes32(uint256(uint160(to)))
                || keccak256(logs[0].data) != keccak256(abi.encode(v))) return "wrong Transfer log";
            if (caller == to) { if (bal(caller) != b0) return "self-transfer changed the balance"; }
            else {
                if (bal(caller) != b0 - v) return "wrong debit";
                if (bal(to) != afterDebitTo + v) return "wrong credit";
            }
        } else {
            if (ok) return "succeeded on a call the post says reverts";
            bytes memory want = debitOk ? errData("ds-math-add-overflow") : errData("ds-math-sub-underflow");
            if (keccak256(out) != keccak256(want)) return "wrong revert data";
            if (bal(caller) != b0 || bal(to) != btEff) return "revert changed storage";
        }
        return "";
    }

    function assertPost(bytes memory c, address caller, address to, uint256 b0, uint256 bt, uint256 v) internal {
        string memory why = post(c, caller, to, b0, bt, v);
        assertEq(bytes(why).length, 0, why);
    }

    // Required concrete case 1: balance 2^256-1, value 1, caller == to succeeds, unchanged, Transfer emitted.
    function test_selfTransferMaxBalance() public {
        address c = address(0xBEEF);
        assertPost(code(), c, c, type(uint256).max, 0, 1);
        assertEq(bal(c), type(uint256).max);
    }

    // Required concrete case 2: self-transfer with balance < value reverts with the source's data.
    function test_selfTransferInsufficient() public {
        address c = address(0xCAFE);
        assertPost(code(), c, c, 5, 0, 6);
    }

    function test_distinct() public {
        assertPost(code(), address(0xA11CE), address(0xB0B), 100, 7, 40);
        assertPost(code(), address(0xA11CE), address(0xB0B), 100, type(uint256).max, 1); // recipient overflow
        assertPost(code(), address(0xA11CE), address(0xB0B), 3, 7, 4); // underflow
    }

    function testFuzz_post(address caller, address to, uint256 b0, uint256 bt, uint256 v, bool self) public {
        vm.assume(caller != T && to != T && uint160(caller) > 0x100);
        if (self) to = caller;
        assertPost(code(), caller, to, b0, bt, v);
    }

    // A call with value is outside Valid: the nonpayable function reverts with no data.
    function test_envValueRejected() public {
        address c = address(0xBEEF);
        vm.etch(T, code());
        vm.store(T, slot(c), bytes32(uint256(10)));
        vm.deal(c, 1);
        vm.prank(c);
        (bool ok, bytes memory out) = T.call{value: 1}(abi.encodeWithSelector(0xa9059cbb, c, 1));
        assertFalse(ok); assertEq(out.length, 0); assertEq(bal(c), 10);
    }

    // ---------------- negative controls by execution ----------------
    function mutate(uint256 at, bytes memory with) internal view returns (bytes memory c) {
        c = code();
        for (uint256 i; i < with.length; i++) c[at + i] = with[i];
    }

    /// Missing debit: SWAP1 SSTORE at 0x426 replaced by POP POP: the post refuses it.
    function test_neg_missingDebit() public {
        bytes memory m = mutate(0x426, hex"5050");
        string memory why = post(m, address(0xA11CE), address(0xB0B), 100, 7, 40);
        assertEq(why, "wrong debit");
    }

    /// Altered jump: the overflow branch's target 0x0466 retargeted to the underflow block 0x0405.
    function test_neg_alteredJump() public {
        bytes memory m = mutate(0x438, hex"0405");
        string memory why = post(m, address(0xA11CE), address(0xB0B), 100, type(uint256).max, 1);
        assertEq(why, "wrong revert data");
    }

    /// Wrong post: the non-sequential post (credit from the recipient's old balance, overflow check
    /// even when caller == to) predicts a revert on the 2^256-1 self-transfer; the bytes succeed.
    function test_neg_wrongPost() public {
        address c = address(0xBEEF);
        vm.etch(T, code());
        vm.store(T, slot(c), bytes32(type(uint256).max));
        vm.prank(c);
        (bool ok,) = T.call(abi.encodeWithSelector(0xa9059cbb, c, 1));
        bool wrongPostPredictsSuccess = type(uint256).max <= type(uint256).max - 1; // bt + v < 2^256 fails
        assertTrue(ok);
        assertTrue(ok != wrongPostPredictsSuccess);
    }
}

