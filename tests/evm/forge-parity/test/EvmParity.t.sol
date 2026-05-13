// SPDX-License-Identifier: MIT
pragma solidity ^0.8.30;

interface Vm {
    struct Log {
        bytes32[] topics;
        bytes data;
        address emitter;
    }

    struct Gas {
        uint64 gasLimit;
        uint64 gasTotalUsed;
        uint64 gasMemoryUsed;
        int64 gasRefunded;
        uint64 gasRemaining;
    }

    function ffi(string[] calldata command) external returns (bytes memory result);
    function lastCallGas() external view returns (Gas memory gas);
    function store(address target, bytes32 slot, bytes32 value) external;
    function load(address target, bytes32 slot) external view returns (bytes32 value);
    function etch(address target, bytes calldata newRuntimeBytecode) external;
    function coolSlot(address target, bytes32 slot) external;
    function deal(address target, uint256 newBalance) external;
    function getNonce(address target) external view returns (uint64 nonce);
    function addr(uint256 privateKey) external returns (address keyAddr);
    function sign(uint256 privateKey, bytes32 digest) external returns (uint8 v, bytes32 r, bytes32 s);
    function roll(uint256 newHeight) external;
    function setBlockhash(uint256 blockNumber, bytes32 blockHash) external;
    function txGasPrice(uint256 newGasPrice) external;
    function prevrandao(uint256 newPrevrandao) external;
    function blobBaseFee(uint256 newBlobBaseFee) external;
    function blobhashes(bytes32[] calldata hashes) external;
    function recordLogs() external;
    function getRecordedLogs() external view returns (Log[] memory logs);
}

contract ComplexParitySubject {
    uint256 public total;
    uint256 public seed;
    uint256 public flag;

    event Mixed(uint256 indexed rounds, uint256 indexed mode, uint256 value, uint256 seed);

    error TooSmall(uint256 got, uint256 need);

    function pureLoop(uint256 rounds, uint256 x) external pure returns (uint256) {
        uint256 acc = x + 3;
        for (uint256 i = 0; i < rounds; i++) {
            if (i & 1 == 0) {
                acc = (acc * 3 + i) ^ (acc >> 1);
            } else {
                acc = (acc + i * 7) ^ (acc << 2);
            }

            if (acc & 0xff == 0x42) {
                acc += 0x99;
            } else if (acc & 0x0f == 0x0a) {
                acc ^= 0x1234;
            } else {
                acc += rounds - i;
            }
        }

        uint256 j = rounds;
        while (j > 0) {
            acc = (acc ^ j) + (j << 3);
            unchecked {
                j--;
            }
        }
        return acc;
    }

    function memoryCrunch(uint256 a, uint256 b, uint256 rounds)
        external
        pure
        returns (uint256 sum, uint256 folded, uint256 last)
    {
        uint256[8] memory ring;
        ring[0] = a;
        ring[1] = b;
        sum = a + b;

        for (uint256 i = 2; i < rounds + 2; i++) {
            uint256 left = ring[(i - 1) & 7];
            uint256 right = ring[(i - 2) & 7];
            uint256 next = left + right + i * 11;
            ring[i & 7] = next;
            sum += next;
            folded ^= (next << (i & 7)) | (next >> ((i + 1) & 7));
        }

        last = ring[(rounds + 1) & 7];
    }

    function bytesLoop(bytes calldata data, uint256 salt) external pure returns (uint256 acc) {
        acc = salt ^ data.length;
        for (uint256 i = 0; i < data.length; i++) {
            uint256 value = uint8(data[i]);
            if (value & 1 == 0) {
                acc += value * (i + 1);
            } else {
                acc ^= value << (i & 15);
            }
            acc = (acc << 1) ^ (acc >> 3) ^ 0x55;
        }
    }

    function storageMix(uint256 rounds, uint256 inc) external returns (uint256 out) {
        uint256 local = total;
        uint256 localSeed = seed;

        for (uint256 i = 0; i < rounds; i++) {
            local += inc + i;
            if (local & 1 == 0) {
                localSeed ^= local + (i << 4);
            } else {
                localSeed += (local ^ i) & 0xffff;
            }
        }

        flag = (localSeed & 1) + rounds;
        total = local;
        seed = localSeed;
        emit Mixed(rounds, flag, local, localSeed);
        return local ^ localSeed ^ flag;
    }

    function guarded(uint256 value, uint256 minimum) external pure returns (uint256) {
        if (value < minimum) {
            revert TooSmall(value, minimum);
        }
        return (value - minimum) * 17 + 1;
    }
}

interface IWorkerParitySubject {
    function total() external view returns (uint256);
    function seed() external view returns (uint256);
    function bump(uint256 rounds, uint256 inc) external returns (uint256);
    function takeValue(uint256 rounds) external payable returns (uint256);
    function readSum(uint256 rounds) external view returns (uint256);
    function failWith(uint256 value) external pure;
    function writeThenRevert(uint256 value) external;
    function logOnly(uint256 value) external returns (uint256);
}

contract WorkerParitySubject {
    uint256 public total;
    uint256 public seed;

    event WorkerTouched(address indexed caller, uint256 indexed rounds, uint256 total, uint256 seed);

    error WorkerError(uint256 value);

    function bump(uint256 rounds, uint256 inc) external returns (uint256 out) {
        uint256 local = total;
        uint256 localSeed = seed;
        for (uint256 i = 0; i < rounds; i++) {
            local += inc + i;
            if (local & 1 == 0) {
                localSeed ^= local + (i << 5);
            } else {
                localSeed += (local ^ i) & 0xffff;
            }
        }
        total = local;
        seed = localSeed;
        emit WorkerTouched(msg.sender, rounds, local, localSeed);
        return local ^ localSeed;
    }

    function takeValue(uint256 rounds) external payable returns (uint256 out) {
        uint256 local = total + msg.value;
        uint256 localSeed = seed ^ address(this).balance;
        for (uint256 i = 0; i < rounds; i++) {
            local += i + 1;
            localSeed = (localSeed + local) ^ (i << 6);
        }
        total = local;
        seed = localSeed;
        emit WorkerTouched(msg.sender, rounds, local, localSeed);
        return local ^ localSeed ^ address(this).balance;
    }

    function readSum(uint256 rounds) external view returns (uint256 out) {
        out = total + seed + rounds;
        for (uint256 i = 0; i < rounds; i++) {
            out = (out + i * 13) ^ (out >> 2);
        }
    }

    function failWith(uint256 value) external pure {
        revert WorkerError(value);
    }

    function writeThenRevert(uint256 value) external {
        total = value;
        seed = value + 1;
        // Avoid emitted logs here: Foundry's recordLogs captures reverted child-frame logs,
        // while committed EVM receipt logs discard them.
        revert WorkerError(value);
    }

    function logOnly(uint256 value) external returns (uint256) {
        emit WorkerTouched(msg.sender, value, total, seed);
        return value + total + seed;
    }
}

contract DelegateParityLib {
    event DelegateTouched(address indexed caller, uint256 value, uint256 result);

    function writeViaDelegate(uint256 value) external returns (uint256) {
        uint256 next = value * 3 + 11;
        assembly {
            sstore(0, next)
        }
        emit DelegateTouched(msg.sender, value, next);
        return next;
    }

    function writeViaCallcode(uint256 value) external payable returns (uint256) {
        uint256 next = value * 5 + msg.value + address(this).balance + 17;
        assembly {
            sstore(0, next)
        }
        emit DelegateTouched(msg.sender, msg.value, next);
        return next ^ address(this).balance;
    }
}

contract MultiCallerParitySubject {
    address internal constant WORKER = 0x2000000000000000000000000000000000000002;
    address internal constant DELEGATE_LIB = 0x3000000000000000000000000000000000000003;

    uint256 public localTotal;
    uint256 public last;

    event CallerTouched(uint256 indexed mode, uint256 value);

    function callWorker(uint256 rounds, uint256 inc) external returns (uint256) {
        uint256 beforeValue = IWorkerParitySubject(WORKER).readSum(3);
        uint256 workerValue = IWorkerParitySubject(WORKER).bump(rounds, inc);
        last = beforeValue + workerValue + localTotal;
        emit CallerTouched(1, last);
        return last;
    }

    function sendValueToWorker(uint256 amount, uint256 rounds) external returns (uint256) {
        uint256 workerValue = IWorkerParitySubject(WORKER).takeValue{value: amount}(rounds);
        last = workerValue + address(this).balance;
        emit CallerTouched(4, last);
        return last;
    }

    function failedValueTransfer(uint256 amount, uint256 rounds)
        external
        returns (uint256 workerTotal, uint256 workerSeed, uint256 length)
    {
        (bool ok, bytes memory data) =
            WORKER.call{value: amount}(abi.encodeCall(IWorkerParitySubject.takeValue, (rounds)));
        require(!ok, "unexpected ok");
        workerTotal = IWorkerParitySubject(WORKER).total();
        workerSeed = IWorkerParitySubject(WORKER).seed();
        length = data.length;
        last = workerTotal + workerSeed + length + address(this).balance;
        emit CallerTouched(9, last);
    }

    function staticWorker(uint256 rounds) external view returns (uint256) {
        return IWorkerParitySubject(WORKER).readSum(rounds) + localTotal;
    }

    function catchWorkerRevert(uint256 value) external returns (uint256 length, bytes4 selector) {
        (bool ok, bytes memory data) = WORKER.call(abi.encodeCall(IWorkerParitySubject.failWith, (value)));
        if (ok) {
            last = 0;
            return (0, bytes4(0));
        }
        bytes4 sel;
        assembly {
            sel := mload(add(data, 32))
        }
        last = data.length;
        emit CallerTouched(2, data.length);
        return (data.length, sel);
    }

    function catchWorkerStorageRevert(uint256 value)
        external
        returns (uint256 workerTotal, uint256 workerSeed, uint256 length)
    {
        (bool ok, bytes memory data) = WORKER.call(abi.encodeCall(IWorkerParitySubject.writeThenRevert, (value)));
        require(!ok, "unexpected ok");
        workerTotal = IWorkerParitySubject(WORKER).total();
        workerSeed = IWorkerParitySubject(WORKER).seed();
        length = data.length;
        last = workerTotal + workerSeed + length;
        emit CallerTouched(5, last);
    }

    function staticWriteFails(uint256 rounds, uint256 inc)
        external
        returns (uint256 workerTotal, uint256 workerSeed, uint256 length)
    {
        (bool ok, bytes memory data) = WORKER.staticcall(abi.encodeCall(IWorkerParitySubject.bump, (rounds, inc)));
        require(!ok, "unexpected ok");
        workerTotal = IWorkerParitySubject(WORKER).total();
        workerSeed = IWorkerParitySubject(WORKER).seed();
        length = data.length;
        last = workerTotal + workerSeed + length;
        emit CallerTouched(6, last);
    }

    function staticLogFails(uint256 value) external returns (uint256 workerTotal, uint256 workerSeed, uint256 length) {
        (bool ok, bytes memory data) = WORKER.staticcall(abi.encodeCall(IWorkerParitySubject.logOnly, (value)));
        require(!ok, "unexpected ok");
        workerTotal = IWorkerParitySubject(WORKER).total();
        workerSeed = IWorkerParitySubject(WORKER).seed();
        length = data.length;
        last = workerTotal + workerSeed + length;
        emit CallerTouched(8, last);
    }

    function delegateWrite(uint256 value) external returns (uint256) {
        (bool ok, bytes memory data) =
            DELEGATE_LIB.delegatecall(abi.encodeWithSignature("writeViaDelegate(uint256)", value));
        require(ok, "delegate failed");
        uint256 written = abi.decode(data, (uint256));
        last = written + localTotal;
        emit CallerTouched(3, last);
        return last;
    }

    function callcodeWrite(uint256 value, uint256 callValue) external returns (uint256) {
        bytes memory input = abi.encodeWithSignature("writeViaCallcode(uint256)", value);
        bytes memory output = new bytes(32);
        address lib = DELEGATE_LIB;
        bool ok;
        assembly {
            ok := callcode(gas(), lib, callValue, add(input, 32), mload(input), add(output, 32), 32)
        }
        require(ok, "callcode failed");
        uint256 written = abi.decode(output, (uint256));
        last = written + localTotal + address(this).balance;
        emit CallerTouched(7, last);
        return last;
    }
}

contract CreatedParitySubject {
    uint256 public value;

    event ConstructorTouched(address indexed caller, uint256 value);
    event RuntimeTouched(address indexed caller, uint256 rounds, uint256 value);

    constructor(uint256 seed) payable {
        value = seed + msg.value;
        emit ConstructorTouched(msg.sender, value);
    }

    function touch(uint256 rounds, uint256 inc) external returns (uint256 out) {
        uint256 local = value;
        for (uint256 i = 0; i < rounds; i++) {
            local += inc + i;
            local = (local ^ (i << 7)) + address(this).balance;
        }
        value = local;
        emit RuntimeTouched(msg.sender, rounds, local);
        return local ^ address(this).balance;
    }
}

contract CreateParityFactory {
    address public lastCreated;
    uint256 public lastValue;

    event FactoryDeployed(address indexed created, uint256 value);

    function deployCreate(uint256 amount, uint256 seed, uint256 rounds, uint256 inc)
        external
        returns (address created, uint256 out)
    {
        CreatedParitySubject child = new CreatedParitySubject{value: amount}(seed);
        created = address(child);
        out = child.touch(rounds, inc);
        lastCreated = created;
        lastValue = out;
        emit FactoryDeployed(created, out);
    }

    function deployCreate2(bytes32 salt, uint256 amount, uint256 seed, uint256 rounds, uint256 inc)
        external
        returns (address created, uint256 out)
    {
        CreatedParitySubject child = new CreatedParitySubject{salt: salt, value: amount}(seed);
        created = address(child);
        out = child.touch(rounds, inc);
        lastCreated = created;
        lastValue = out;
        emit FactoryDeployed(created, out);
    }

    function tryCreate2(bytes32 salt, bytes memory initCode) external returns (address created, uint256 marker) {
        assembly {
            created := create2(0, add(initCode, 32), mload(initCode), salt)
        }
        marker = created == address(0) ? 1 : 2;
    }
}

contract PrecompileParitySubject {
    function identity(bytes calldata input) external view returns (bool ok, bytes memory output) {
        return address(4).staticcall(input);
    }

    function sha256Precompile(bytes calldata input) external view returns (bool ok, bytes memory output) {
        return address(2).staticcall(input);
    }

    function sha256PrecompileWithGas(bytes calldata input, uint256 gasAmount)
        external
        view
        returns (bool ok, bytes memory output)
    {
        return address(2).staticcall{gas: gasAmount}(input);
    }

    function ripemd160Precompile(bytes calldata input) external view returns (bool ok, bytes memory output) {
        return address(3).staticcall(input);
    }

    function ripemd160PrecompileWithGas(bytes calldata input, uint256 gasAmount)
        external
        view
        returns (bool ok, bytes memory output)
    {
        return address(3).staticcall{gas: gasAmount}(input);
    }

    function modexpPrecompile(bytes calldata input) external view returns (bool ok, bytes memory output) {
        return address(5).staticcall(input);
    }

    function modexpPrecompileWithGas(bytes calldata input, uint256 gasAmount)
        external
        view
        returns (bool ok, bytes memory output)
    {
        return address(5).staticcall{gas: gasAmount}(input);
    }

    function ecaddPrecompile(bytes calldata input) external view returns (bool ok, bytes memory output) {
        return address(6).staticcall(input);
    }

    function ecaddPrecompileWithGas(bytes calldata input, uint256 gasAmount)
        external
        view
        returns (bool ok, bytes memory output)
    {
        return address(6).staticcall{gas: gasAmount}(input);
    }

    function ecmulPrecompile(bytes calldata input) external view returns (bool ok, bytes memory output) {
        return address(7).staticcall(input);
    }

    function ecmulPrecompileWithGas(bytes calldata input, uint256 gasAmount)
        external
        view
        returns (bool ok, bytes memory output)
    {
        return address(7).staticcall{gas: gasAmount}(input);
    }

    function ecpairingPrecompile(bytes calldata input) external view returns (bool ok, bytes memory output) {
        return address(8).staticcall(input);
    }

    function ecpairingPrecompileWithGas(bytes calldata input, uint256 gasAmount)
        external
        view
        returns (bool ok, bytes memory output)
    {
        return address(8).staticcall{gas: gasAmount}(input);
    }

    function blake2fPrecompile(bytes calldata input) external view returns (bool ok, bytes memory output) {
        return address(9).staticcall(input);
    }

    function blake2fPrecompileWithGas(bytes calldata input, uint256 gasAmount)
        external
        view
        returns (bool ok, bytes memory output)
    {
        return address(9).staticcall{gas: gasAmount}(input);
    }

    function pointEvaluationPrecompile(bytes calldata input) external view returns (bool ok, bytes memory output) {
        return address(10).staticcall(input);
    }

    function pointEvaluationPrecompileWithGas(bytes calldata input, uint256 gasAmount)
        external
        view
        returns (bool ok, bytes memory output)
    {
        return address(10).staticcall{gas: gasAmount}(input);
    }

    function p256VerifyPrecompile(bytes calldata input) external view returns (bool ok, bytes memory output) {
        return address(0x100).staticcall(input);
    }

    function p256VerifyPrecompileWithGas(bytes calldata input, uint256 gasAmount)
        external
        view
        returns (bool ok, bytes memory output)
    {
        return address(0x100).staticcall{gas: gasAmount}(input);
    }

    function precompileAt(address precompile, bytes calldata input)
        external
        view
        returns (bool ok, bytes memory output)
    {
        return precompile.staticcall(input);
    }

    function precompileAtWithGas(address precompile, bytes calldata input, uint256 gasAmount)
        external
        view
        returns (bool ok, bytes memory output)
    {
        return precompile.staticcall{gas: gasAmount}(input);
    }

    function precompileAtDelegatecall(address precompile, bytes calldata input)
        external
        returns (bool ok, bytes memory output, uint256 selfBalance, uint256 precompileBalance)
    {
        (ok, output) = precompile.delegatecall(input);
        return (ok, output, address(this).balance, precompile.balance);
    }

    function precompileAtCallcode(address precompile, bytes calldata input, uint256 amount)
        external
        payable
        returns (bool ok, bytes memory output, uint256 selfBalance, uint256 precompileBalance)
    {
        bytes memory data = input;
        output = new bytes(data.length);
        assembly {
            ok := callcode(gas(), precompile, amount, add(data, 32), mload(data), add(output, 32), mload(output))
        }
        return (ok, output, address(this).balance, precompile.balance);
    }

    function precompileAtWithValue(address precompile, bytes calldata input, uint256 amount)
        external
        payable
        returns (bool ok, bytes memory output, uint256 precompileBalance, uint256 selfBalance)
    {
        (ok, output) = precompile.call{value: amount}(input);
        return (ok, output, precompile.balance, address(this).balance);
    }

    function precompileAtWithValueAndGas(address precompile, bytes calldata input, uint256 amount, uint256 gasAmount)
        external
        payable
        returns (bool ok, bytes memory output, uint256 precompileBalance, uint256 selfBalance)
    {
        (ok, output) = precompile.call{value: amount, gas: gasAmount}(input);
        return (ok, output, precompile.balance, address(this).balance);
    }

    function ecrecoverPrecompile(bytes32 digest, uint8 v, bytes32 r, bytes32 s)
        external
        view
        returns (bool ok, bytes memory output)
    {
        return address(1).staticcall(abi.encode(digest, v, r, s));
    }

    function ecrecoverPrecompileWithGas(bytes32 digest, uint8 v, bytes32 r, bytes32 s, uint256 gasAmount)
        external
        view
        returns (bool ok, bytes memory output)
    {
        return address(1).staticcall{gas: gasAmount}(abi.encode(digest, v, r, s));
    }
}

contract EvmParityTest {
    Vm internal constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    address internal constant TARGET = 0x1000000000000000000000000000000000000001;
    address internal constant WORKER = 0x2000000000000000000000000000000000000002;
    address internal constant DELEGATE_LIB = 0x3000000000000000000000000000000000000003;
    address internal constant EMPTY_ACCOUNT = 0x4000000000000000000000000000000000000004;
    uint256 internal constant GAS_LIMIT = 1_000_000;

    struct DynamicCreateCase {
        string name;
        bytes data;
        uint256 rootInitialBalance;
        uint64 rootNonce;
        address expectedCreated;
        string[] keccakAssignments;
    }

    struct BaseCommandCase {
        string name;
        bytes code;
        bytes data;
        bool success;
        bytes output;
        Vm.Gas gas;
        uint256 callValue;
        uint256 initialBalance;
        uint256 expectedBalance;
    }

    function testReturnWordParity() public {
        bytes memory code = hex"602a5f5260205ff3";
        runCase("return-word", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testGasOpcodeParity() public {
        bytes memory code = hex"5a5f5260205ff3";
        runCase("gas-opcode", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testColdSstoreParity() public {
        bytes memory code = hex"602a5f5500";
        bytes32[] memory initialSlots = new bytes32[](0);
        bytes32[] memory checkedSlots = new bytes32[](1);
        checkedSlots[0] = bytes32(uint256(0));
        runCase("cold-sstore", code, hex"", initialSlots, checkedSlots);
    }

    function testSstoreClearRefundParity() public {
        bytes memory code = hex"5f5f5500";
        bytes32[] memory initialSlots = new bytes32[](1);
        initialSlots[0] = bytes32(uint256(5));
        bytes32[] memory checkedSlots = new bytes32[](1);
        checkedSlots[0] = bytes32(uint256(0));
        runCase("sstore-clear-refund", code, hex"", initialSlots, checkedSlots);
    }

    function testSstoreDirtyNoopParity() public {
        bytes memory code = hex"60055f5500";
        bytes32[] memory initialSlots = new bytes32[](1);
        initialSlots[0] = bytes32(uint256(5));
        bytes32[] memory checkedSlots = new bytes32[](1);
        checkedSlots[0] = bytes32(uint256(0));
        runCase("sstore-dirty-noop", code, hex"", initialSlots, checkedSlots);
    }

    function testSstoreSetThenResetRefundParity() public {
        bytes memory code = hex"60075f555f5f5500";
        bytes32[] memory checkedSlots = new bytes32[](1);
        checkedSlots[0] = bytes32(uint256(0));
        runCase("sstore-set-then-reset-refund", code, hex"", new bytes32[](0), checkedSlots);
    }

    function testColdSloadParity() public {
        bytes memory code = hex"5f545f5260205ff3";
        bytes32[] memory initialSlots = new bytes32[](1);
        initialSlots[0] = bytes32(uint256(7));
        bytes32[] memory checkedSlots = new bytes32[](1);
        checkedSlots[0] = bytes32(uint256(0));
        runCase("cold-sload", code, hex"", initialSlots, checkedSlots);
    }

    function testWarmSloadParity() public {
        bytes memory code = hex"5f545f525f5460205260405ff3";
        bytes32[] memory initialSlots = new bytes32[](1);
        initialSlots[0] = bytes32(uint256(7));
        bytes32[] memory checkedSlots = new bytes32[](1);
        checkedSlots[0] = bytes32(uint256(0));
        runCase("warm-sload", code, hex"", initialSlots, checkedSlots);
    }

    function testLogParity() public {
        bytes memory code = hex"602a5f52600760205fa100";
        runCase("log1", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testLog4Parity() public {
        bytes memory code =
            hex"7f0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f205f52604460336022601160205fa400";
        runCase("log4", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testSelfbalanceParity() public {
        bytes memory code = hex"475f5260205ff3";
        runCaseWithState("selfbalance", code, hex"", 123, 0, new bytes32[](0), new bytes32[](0));
    }

    function testCallContextOpcodeParity() public {
        bytes memory code = hex"305f5233602052326040523460605260805ff3";
        runCaseWithState("call-context-opcodes", code, hex"", 123, 77, new bytes32[](0), new bytes32[](0));
    }

    function testBlockContextOpcodeParity() public {
        bytes memory code = hex"415f52426020524360405245606052466080524860a05260c05ff3";
        runCase("block-context-opcodes", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testBlockhashParity() public {
        bytes32 previousHash = 0x111122223333444455556666777788889999aaaabbbbccccddddeeeeffff0000;
        vm.roll(8);
        vm.setBlockhash(7, previousHash);
        bytes memory code = hex"6007405f5260084060205260405ff3";
        string[] memory blockhashes = new string[](1);
        blockhashes[0] = string.concat("7=", wordHex(previousHash));
        runCaseWithBlockhashes("blockhash", code, hex"", blockhashes);
    }

    function testBlobhashParity() public {
        bytes32[] memory hashes = new bytes32[](2);
        hashes[0] = 0xaaaabbbbccccddddeeeeffff0000111122223333444455556666777788889999;
        hashes[1] = 0x9999888877776666555544443333222211110000ffffeeeeddddccccbbbbaaaa;
        vm.blobhashes(hashes);
        bytes memory code = hex"5f495f5260014960205260024960405260605ff3";
        runCaseWithBlobhashes("blobhash", code, hashes);
    }

    function testKeccakMemorySliceParity() public {
        bytes memory code =
            hex"7f0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f205f526021601f205f5260205ff3";
        bytes memory preimage = new bytes(33);
        preimage[0] = bytes1(0x20);
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));
        runCaseWithKeccaks("keccak-memory-slice", code, hex"", keccaks);
    }

    function testZeroLengthMemoryRangeParity() public {
        bytes memory code = hex"5f5f610400395f5f610500375f5f6106003e5f61070020505f610800a0595f5260205ff3";
        bytes memory empty = hex"";
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(empty, keccak256(empty));
        runCaseWithKeccaks("zero-length-memory-ranges", code, hex"", keccaks);
    }

    function testCalldataLoadAndSizeParity() public {
        bytes memory code = hex"5f355f526004356020526020356040523660605260805ff3";
        bytes memory data = hex"11223344556677";
        runCase("calldataload-size-padding", code, data, new bytes32[](0), new bytes32[](0));
    }

    function testPcAndMsizeParity() public {
        bytes memory code = hex"595f52596020525860405260ff6041535960605260805ff3";
        runCase("pc-msize", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testMstore8AndMloadParity() public {
        bytes memory code =
            hex"7f0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f205f526112346001535f5160405260015160605260406040f3";
        runCase("mstore8-mload", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testFeeAndRandomContextOpcodeParity() public {
        uint256 gasPrice = 123456789;
        uint256 prevrandaoValue = 0x123456789abc;
        vm.txGasPrice(gasPrice);
        vm.prevrandao(prevrandaoValue);
        uint256 blobBaseFee = block.blobbasefee;
        bytes memory code = hex"3a5f52446020524a60405260605ff3";
        runCaseWithFeeContext("fee-random-context-opcodes", code, gasPrice, prevrandaoValue, blobBaseFee);
    }

    function testBalanceExistingAndMissingParity() public {
        vm.deal(WORKER, 12345);
        bytes memory code =
            hex"732000000000000000000000000000000000000002315f527340000000000000000000000000000000000000043160205260405ff3";
        string[] memory accountBalances = new string[](1);
        accountBalances[0] = string.concat(addressArg(WORKER), "=12345");
        address[] memory warmAddresses = new address[](1);
        warmAddresses[0] = WORKER;
        runCaseWithAccountBalances("balance-existing-missing", code, hex"", accountBalances, warmAddresses);
    }

    function testExtCodeHashSelfParity() public {
        bytes memory code = hex"303f5f5260205ff3";
        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(code, keccak256(code));
        runCaseWithKeccaks("extcodehash-self", code, hex"", keccaks);
    }

    function testExtCodeHashMissingAccountParity() public {
        bytes memory code = hex"7340000000000000000000000000000000000000043f5f5260205ff3";
        runCase("extcodehash-missing-account", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testExtCodeHashEmptyAccountParity() public {
        vm.deal(EMPTY_ACCOUNT, 1);
        bytes memory code = hex"7340000000000000000000000000000000000000043f5f5260205ff3";
        string[] memory accountBalances = new string[](1);
        accountBalances[0] = string.concat(addressArg(EMPTY_ACCOUNT), "=1");
        address[] memory warmAddresses = new address[](1);
        warmAddresses[0] = EMPTY_ACCOUNT;
        runCaseWithAccountBalances("extcodehash-empty-account", code, hex"", accountBalances, warmAddresses);
    }

    function testCallZeroValueMissingAccountDoesNotMaterializeParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f15f527320000000000000000000000000000000000000023f60205260405ff3";
        runCase("call-zero-value-missing-account-not-materialized", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testCallMissingAccountClearsReturndataParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f15f523d6020525f5f5f5f5f734000000000000000000000000000000000000004620f4240f16040523d6060527340000000000000000000000000000000000000043f60805260a05ff3";
        bytes memory accountCode = hex"602a5f5260205ff3";
        runCaseWithAccountCode("call-missing-account-clears-returndata", code, hex"", WORKER, accountCode);
    }

    function testExtCodeSizeAndCopyParity() public {
        bytes memory code =
            hex"7320000000000000000000000000000000000000023b5f5260046001602073200000000000000000000000000000000000000000023c60405ff3";
        bytes memory accountCode = hex"6011602255fe7f";
        runCaseWithAccountCode("extcodesize-extcodecopy", code, hex"", WORKER, accountCode);
    }

    function testRevertParity() public {
        bytes memory code = hex"602a5f5260205ffd";
        runCase("revert-word", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testInvalidOpcodeParity() public {
        runCaseSkippingGas("invalid-opcode", hex"fe", hex"", new bytes32[](0), new bytes32[](0));
    }

    function testStackUnderflowParity() public {
        runCaseSkippingGas("stack-underflow", hex"50", hex"", new bytes32[](0), new bytes32[](0));
    }

    function testStackOverflowParity() public {
        bytes memory code = new bytes(1025);
        for (uint256 i = 0; i < code.length; i++) {
            code[i] = 0x5f;
        }
        runCaseSkippingGas("stack-overflow", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testMemoryExpansionOutOfGasParity() public {
        runCaseSkippingGas("memory-expansion-oog", hex"600162ffffff52", hex"", new bytes32[](0), new bytes32[](0));
    }

    function testBadJumpParity() public {
        runCaseSkippingGas("bad-jump", hex"600156", hex"", new bytes32[](0), new bytes32[](0));
    }

    function testValidJumpAndJumpiParity() public {
        bytes memory code = hex"5f60115760115f52600160115760ff5f525b6022602052601f5660ee6020525b603360405260605ff3";
        runCase("valid-jump-jumpi", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testReturndataCopyOutOfBoundsParity() public {
        bytes memory code = hex"600160005f3e00";
        runCaseSkippingGas("returndatacopy-oob", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testRawCallReturndataParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f16040523d5f5260205f60203e60605ff3";
        bytes memory accountCode = hex"602a5f5260205ff3";
        runCaseWithAccountCode("raw-call-returndata", code, hex"", WORKER, accountCode);
    }

    function testRawCallOutputTruncationParity() public {
        bytes memory code =
            hex"60045f5f5f5f732000000000000000000000000000000000000002620f4240f16040523d6020523d5f60603e60805ff3";
        bytes memory accountCode = hex"7f0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f205f5260205ff3";
        runCaseWithAccountCode("raw-call-output-truncation", code, hex"", WORKER, accountCode);
    }

    function testCallValueCreatesEmptyAccountParity() public {
        bytes memory code = hex"5f5f5f5f6104d2732000000000000000000000000000000000000002620f4240f15f5260205ff3";
        runCallValueNewAccountCase("call-value-new-empty-account", code, 5000);
    }

    function testCreateRevertReturndataParity() public {
        bytes memory initCode = hex"602a5f5260205ffd";
        bytes memory code = hex"6008601a5f3960085f5ff05f523d6020523d5f60403e60605ff3602a5f5260205ffd";
        runCreateRevertCase("create-revert-returndata", code, initCode);
    }

    function testCreateCodeDepositOutOfGasParity() public {
        bytes memory code = hex"6005601a5f3960055f5ff05f523d6020523d5f60403e60605ff36117705ff3";
        runCreateFailureCase("create-code-deposit-oog", code);
    }

    function testCreateSuccessClearsReturndataParity() public {
        bytes memory code = hex"600b60155f39600b5f5ff05f523d60205260405ff36001600a5f3960015ff300";
        runCreateResultCase("create-success-clears-returndata", code, hex"00");
    }

    function testSelfdestructExistingAccountParity() public {
        bytes memory code = hex"732000000000000000000000000000000000000002ff";
        bytes32[] memory initialSlots = new bytes32[](2);
        initialSlots[0] = bytes32(uint256(0x1234));
        initialSlots[1] = bytes32(uint256(0x5678));

        bytes32[] memory checkedSlots = new bytes32[](2);
        checkedSlots[0] = bytes32(uint256(0));
        checkedSlots[1] = bytes32(uint256(1));

        runSelfdestructExistingCase("selfdestruct-existing", code, 2468, initialSlots, checkedSlots);
    }

    function testSelfdestructNewAccountParity() public {
        bytes memory code = hex"732000000000000000000000000000000000000002ff";
        runCallValueNewAccountCase("selfdestruct-new-account", code, 2468);
    }

    function testSelfdestructSelfExistingAccountParity() public {
        bytes memory code = hex"30ff";
        bytes32[] memory initialSlots = new bytes32[](1);
        initialSlots[0] = bytes32(uint256(0x1234));
        bytes32[] memory checkedSlots = new bytes32[](1);
        checkedSlots[0] = bytes32(uint256(0));
        runCaseWithState("selfdestruct-self-existing", code, hex"", 2468, 0, initialSlots, checkedSlots);
    }

    function testStaticcallSelfdestructFailsParity() public {
        bytes memory code = hex"5f5f5f5f732000000000000000000000000000000000000002620f4240fa5f5260205ff3";
        bytes memory accountCode = hex"732000000000000000000000000000000000000002ff";
        runCaseWithAccountCode("staticcall-selfdestruct-fails", code, hex"", WORKER, accountCode);
    }

    function testCodeAndCalldataCopyParity() public {
        bytes memory code = hex"60106000600039365f602037386060523660805260a05ff3";
        bytes memory data = hex"112233445566778899aabbccddeeff0011223344556677";
        runCase("code-calldata-copy", code, data, new bytes32[](0), new bytes32[](0));
    }

    function testCodesizeAndShortCodecopyParity() public {
        bytes memory code = hex"385f5260045f60203960405ff3";
        runCase("codesize-short-codecopy", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testTransientStorageParity() public {
        bytes memory code = hex"60ab5f5d5f5c5f5260205ff3";
        runCase("transient-storage", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testMcopyOverlapParity() public {
        bytes memory code =
            hex"7f0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f205f52601f5f60015e60205ff3";
        runCase("mcopy-overlap", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testWordOperandOrderParity() public {
        bytes memory code =
            hex"60036005035f526014600304602052601460060660405260036005106060526003600511608052600260071b60a05261010060041c60c05260e05ff3";
        runCase("word-operand-order", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testDeepDupAndSwapParity() public {
        bytes memory code =
            hex"600160026003600460056006600760086009600a600b600c600d600e600f601060119f8f5f5260205260405260605ff3";
        runCase("deep-dup-swap", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testTernaryAndSignParity() public {
        bytes memory code = hex"600260076005085f5260036007600509602052600260050a6040525f60800b60605260805ff3";
        runCase("ternary-sign-order", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testSignedAndBitOpcodeParity() public {
        bytes memory code =
            hex"6002600719055f5260036006190760205260015f19126040525f1960011360605260071960011d60805260805f0b60a0527f0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20601f1a60c0525f1960e0525f15610100526101205ff3";
        runCase("signed-bit-opcodes", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testArithmeticAndBitEdgeParity() public {
        bytes memory code =
            hex"5f6007045f525f6007066020525f60076005086040525f60076005096060525f197f8000000000000000000000000000000000000000000000000000000000000000056080525f6006190760a05260016101001b60c0525f196101001c60e0525f196101001d610100525f1960201a61012052608060200b610140526101605ff3";
        runCase("arithmetic-bit-edges", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testClzParity() public {
        bytes memory code =
            hex"5f1e5f5260011e60205260ff1e6040527f80000000000000000000000000000000000000000000000000000000000000001e60605260805ff3";
        runCase("clz", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testComplexPureLoopContractParity() public {
        runCase(
            "complex-pure-loop",
            type(ComplexParitySubject).runtimeCode,
            abi.encodeCall(ComplexParitySubject.pureLoop, (19, 7)),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testComplexMemoryCrunchContractParity() public {
        runCase(
            "complex-memory-crunch",
            type(ComplexParitySubject).runtimeCode,
            abi.encodeCall(ComplexParitySubject.memoryCrunch, (9, 13, 12)),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testComplexBytesLoopContractParity() public {
        runCase(
            "complex-bytes-loop",
            type(ComplexParitySubject).runtimeCode,
            abi.encodeCall(ComplexParitySubject.bytesLoop, (hex"00112233445566778899aabbccddeeff", 0x1234)),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testComplexStorageAndLogContractParity() public {
        bytes32[] memory initialSlots = new bytes32[](3);
        initialSlots[0] = bytes32(uint256(3));
        initialSlots[1] = bytes32(uint256(11));
        initialSlots[2] = bytes32(uint256(0));

        bytes32[] memory checkedSlots = new bytes32[](3);
        checkedSlots[0] = bytes32(uint256(0));
        checkedSlots[1] = bytes32(uint256(1));
        checkedSlots[2] = bytes32(uint256(2));

        runCase(
            "complex-storage-log",
            type(ComplexParitySubject).runtimeCode,
            abi.encodeCall(ComplexParitySubject.storageMix, (8, 5)),
            initialSlots,
            checkedSlots
        );
    }

    function testComplexCustomErrorRevertContractParity() public {
        runCase(
            "complex-custom-error",
            type(ComplexParitySubject).runtimeCode,
            abi.encodeCall(ComplexParitySubject.guarded, (5, 9)),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testMultiContractCallAndStaticCallParity() public {
        bytes32[] memory rootInitialSlots = new bytes32[](2);
        rootInitialSlots[0] = bytes32(uint256(17));
        rootInitialSlots[1] = bytes32(uint256(0));

        bytes32[] memory rootCheckedSlots = new bytes32[](2);
        rootCheckedSlots[0] = bytes32(uint256(0));
        rootCheckedSlots[1] = bytes32(uint256(1));

        bytes32[] memory workerInitialSlots = new bytes32[](2);
        workerInitialSlots[0] = bytes32(uint256(5));
        workerInitialSlots[1] = bytes32(uint256(9));

        bytes32[] memory workerCheckedSlots = new bytes32[](2);
        workerCheckedSlots[0] = bytes32(uint256(0));
        workerCheckedSlots[1] = bytes32(uint256(1));

        runMultiCase(
            "multi-call-static",
            abi.encodeCall(MultiCallerParitySubject.callWorker, (6, 4)),
            rootInitialSlots,
            rootCheckedSlots,
            workerInitialSlots,
            workerCheckedSlots
        );
    }

    function testMultiContractStaticOnlyParity() public {
        bytes32[] memory workerInitialSlots = new bytes32[](2);
        workerInitialSlots[0] = bytes32(uint256(21));
        workerInitialSlots[1] = bytes32(uint256(34));

        runMultiCase(
            "multi-static-only",
            abi.encodeCall(MultiCallerParitySubject.staticWorker, (9)),
            new bytes32[](0),
            new bytes32[](0),
            workerInitialSlots,
            new bytes32[](0)
        );
    }

    function testMultiContractStaticWriteFailsParity() public {
        bytes32[] memory rootCheckedSlots = new bytes32[](1);
        rootCheckedSlots[0] = bytes32(uint256(1));

        bytes32[] memory workerInitialSlots = new bytes32[](2);
        workerInitialSlots[0] = bytes32(uint256(21));
        workerInitialSlots[1] = bytes32(uint256(34));

        bytes32[] memory workerCheckedSlots = new bytes32[](2);
        workerCheckedSlots[0] = bytes32(uint256(0));
        workerCheckedSlots[1] = bytes32(uint256(1));

        runMultiCase(
            "multi-static-write-fails",
            abi.encodeCall(MultiCallerParitySubject.staticWriteFails, (3, 5)),
            new bytes32[](0),
            rootCheckedSlots,
            workerInitialSlots,
            workerCheckedSlots
        );
    }

    function testMultiContractStaticLogFailsParity() public {
        bytes32[] memory rootCheckedSlots = new bytes32[](1);
        rootCheckedSlots[0] = bytes32(uint256(1));

        bytes32[] memory workerInitialSlots = new bytes32[](2);
        workerInitialSlots[0] = bytes32(uint256(21));
        workerInitialSlots[1] = bytes32(uint256(34));

        bytes32[] memory workerCheckedSlots = new bytes32[](2);
        workerCheckedSlots[0] = bytes32(uint256(0));
        workerCheckedSlots[1] = bytes32(uint256(1));

        runMultiCase(
            "multi-static-log-fails",
            abi.encodeCall(MultiCallerParitySubject.staticLogFails, (99)),
            new bytes32[](0),
            rootCheckedSlots,
            workerInitialSlots,
            workerCheckedSlots
        );
    }

    function testMultiContractValueTransferParity() public {
        bytes32[] memory rootCheckedSlots = new bytes32[](1);
        rootCheckedSlots[0] = bytes32(uint256(1));

        bytes32[] memory workerInitialSlots = new bytes32[](2);
        workerInitialSlots[0] = bytes32(uint256(2));
        workerInitialSlots[1] = bytes32(uint256(6));

        bytes32[] memory workerCheckedSlots = new bytes32[](2);
        workerCheckedSlots[0] = bytes32(uint256(0));
        workerCheckedSlots[1] = bytes32(uint256(1));

        vm.deal(TARGET, 5000);
        runMultiCase(
            "multi-value-transfer",
            abi.encodeCall(MultiCallerParitySubject.sendValueToWorker, (1234, 5)),
            new bytes32[](0),
            rootCheckedSlots,
            workerInitialSlots,
            workerCheckedSlots
        );
    }

    function testMultiContractInsufficientBalanceCallParity() public {
        bytes32[] memory rootCheckedSlots = new bytes32[](1);
        rootCheckedSlots[0] = bytes32(uint256(1));

        bytes32[] memory workerInitialSlots = new bytes32[](2);
        workerInitialSlots[0] = bytes32(uint256(2));
        workerInitialSlots[1] = bytes32(uint256(6));

        bytes32[] memory workerCheckedSlots = new bytes32[](2);
        workerCheckedSlots[0] = bytes32(uint256(0));
        workerCheckedSlots[1] = bytes32(uint256(1));

        vm.deal(TARGET, 100);
        runMultiCase(
            "multi-insufficient-balance-call",
            abi.encodeCall(MultiCallerParitySubject.failedValueTransfer, (1234, 5)),
            new bytes32[](0),
            rootCheckedSlots,
            workerInitialSlots,
            workerCheckedSlots
        );
    }

    function testMultiContractCaughtRevertParity() public {
        bytes32[] memory rootCheckedSlots = new bytes32[](1);
        rootCheckedSlots[0] = bytes32(uint256(1));

        runMultiCase(
            "multi-caught-revert",
            abi.encodeCall(MultiCallerParitySubject.catchWorkerRevert, (77)),
            new bytes32[](0),
            rootCheckedSlots,
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testMultiContractRevertRollbackParity() public {
        bytes32[] memory rootCheckedSlots = new bytes32[](1);
        rootCheckedSlots[0] = bytes32(uint256(1));

        bytes32[] memory workerInitialSlots = new bytes32[](2);
        workerInitialSlots[0] = bytes32(uint256(5));
        workerInitialSlots[1] = bytes32(uint256(9));

        bytes32[] memory workerCheckedSlots = new bytes32[](2);
        workerCheckedSlots[0] = bytes32(uint256(0));
        workerCheckedSlots[1] = bytes32(uint256(1));

        runMultiCase(
            "multi-revert-rollback",
            abi.encodeCall(MultiCallerParitySubject.catchWorkerStorageRevert, (12345)),
            new bytes32[](0),
            rootCheckedSlots,
            workerInitialSlots,
            workerCheckedSlots
        );
    }

    function testMultiContractDelegateCallParity() public {
        bytes32[] memory rootInitialSlots = new bytes32[](2);
        rootInitialSlots[0] = bytes32(uint256(4));
        rootInitialSlots[1] = bytes32(uint256(1));

        bytes32[] memory rootCheckedSlots = new bytes32[](2);
        rootCheckedSlots[0] = bytes32(uint256(0));
        rootCheckedSlots[1] = bytes32(uint256(1));

        runMultiCase(
            "multi-delegatecall",
            abi.encodeCall(MultiCallerParitySubject.delegateWrite, (19)),
            rootInitialSlots,
            rootCheckedSlots,
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testMultiContractCallcodeParity() public {
        bytes32[] memory rootInitialSlots = new bytes32[](2);
        rootInitialSlots[0] = bytes32(uint256(7));
        rootInitialSlots[1] = bytes32(uint256(2));

        bytes32[] memory rootCheckedSlots = new bytes32[](2);
        rootCheckedSlots[0] = bytes32(uint256(0));
        rootCheckedSlots[1] = bytes32(uint256(1));

        vm.deal(TARGET, 4321);
        runMultiCase(
            "multi-callcode",
            abi.encodeCall(MultiCallerParitySubject.callcodeWrite, (13, 222)),
            rootInitialSlots,
            rootCheckedSlots,
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testIdentityPrecompileParity() public {
        runCase(
            "identity-precompile",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.identity, (hex"00112233445566778899aabbccddeeff")),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testIdentityPrecompileOutOfGasParity() public {
        bytes memory code =
            hex"7f0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f205f526020604060205f5f6004600af16080523d60a05260405160c05260606080f3";
        runCase("identity-precompile-oog", code, hex"", new bytes32[](0), new bytes32[](0));
    }

    function testIdentityPrecompileCallValueParity() public {
        runCaseWithState(
            "identity-precompile-call-value",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.precompileAtWithValue, (address(4), hex"0011223344", uint256(123))),
            500,
            0,
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testIdentityPrecompileCallValueOutOfGasRollbackParity() public {
        runCaseWithState(
            "identity-precompile-call-value-oog-rollback",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(
                PrecompileParitySubject.precompileAtWithValueAndGas, (address(4), hex"", uint256(123), uint256(14))
            ),
            500,
            0,
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testIdentityPrecompileDelegatecallParity() public {
        runCase(
            "identity-precompile-delegatecall",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.precompileAtDelegatecall, (address(4), hex"0011223344")),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testIdentityPrecompileCallcodeValueParity() public {
        runCaseWithState(
            "identity-precompile-callcode-value",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.precompileAtCallcode, (address(4), hex"0011223344", uint256(123))),
            500,
            0,
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testSha256PrecompileParity() public {
        bytes memory input = hex"00112233445566778899aabbccddeeff0102030405060708090a";
        string[] memory sha256s = new string[](1);
        sha256s[0] = sha256Arg(input, sha256(input));
        runCaseWithSha256s(
            "sha256-precompile",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.sha256Precompile, (input)),
            sha256s
        );
    }

    function testSha256PrecompileOutOfGasParity() public {
        bytes memory input = hex"01";
        runCase(
            "sha256-precompile-oog",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.sha256PrecompileWithGas, (input, uint256(71))),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testRipemd160PrecompileParity() public {
        bytes memory input = hex"ffeeddccbbaa998877665544332211000102030405060708090a0b0c0d";
        string[] memory ripemd160s = new string[](1);
        ripemd160s[0] = ripemd160Arg(input, ripemd160(input));
        runCaseWithRipemd160s(
            "ripemd160-precompile",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.ripemd160Precompile, (input)),
            ripemd160s
        );
    }

    function testRipemd160PrecompileOutOfGasParity() public {
        bytes memory input = hex"01";
        runCase(
            "ripemd160-precompile-oog",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.ripemd160PrecompileWithGas, (input, uint256(719))),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testModexpPrecompileParity() public {
        bytes memory input = abi.encodePacked(
            bytes32(uint256(1)), bytes32(uint256(1)), bytes32(uint256(1)), bytes1(0x02), bytes1(0x05), bytes1(0x0d)
        );
        (bool ok, bytes memory expected) = address(5).staticcall(input);
        require(ok, "modexp precompile failed");

        string[] memory modexps = new string[](1);
        modexps[0] = modexpArg(input, expected);
        runCaseWithModexps(
            "modexp-precompile",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.modexpPrecompile, (input)),
            modexps
        );
    }

    function testModexpPrecompileOutOfGasParity() public {
        bytes memory input = abi.encodePacked(
            bytes32(uint256(1)), bytes32(uint256(1)), bytes32(uint256(1)), bytes1(0x02), bytes1(0x05), bytes1(0x0d)
        );
        runCase(
            "modexp-precompile-oog",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.modexpPrecompileWithGas, (input, uint256(499))),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testModexpZeroModulusParity() public {
        bytes memory input = abi.encodePacked(bytes32(uint256(0)), bytes32(uint256(0)), bytes32(uint256(0)));
        runCase(
            "modexp-zero-modulus",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.modexpPrecompile, (input)),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testEcaddEmptyInputParity() public {
        runCase(
            "ecadd-empty-input",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.ecaddPrecompile, (hex"")),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testEcaddPrecompileParity() public {
        bytes memory input =
            abi.encodePacked(bytes32(uint256(1)), bytes32(uint256(2)), bytes32(uint256(1)), bytes32(uint256(2)));
        (bool ok, bytes memory expected) = address(6).staticcall(input);
        require(ok && expected.length == 64, "ecadd precompile failed");

        string[] memory ecadds = new string[](1);
        ecadds[0] = ecaddArg(input, expected);
        runCaseWithEcadds(
            "ecadd-precompile",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.ecaddPrecompile, (input)),
            ecadds
        );
    }

    function testEcaddPrecompileOutOfGasParity() public {
        runCase(
            "ecadd-precompile-oog",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.ecaddPrecompileWithGas, (hex"", uint256(149))),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testEcaddInvalidPointParity() public {
        bytes memory input =
            abi.encodePacked(bytes32(uint256(1)), bytes32(uint256(1)), bytes32(uint256(0)), bytes32(uint256(0)));
        string[] memory failures = new string[](1);
        failures[0] = hexString(input);
        runCaseWithBn254Failures(
            "ecadd-invalid-point",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.ecaddPrecompile, (input)),
            failures,
            new string[](0),
            new string[](0)
        );
    }

    function testEcmulEmptyInputParity() public {
        runCase(
            "ecmul-empty-input",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.ecmulPrecompile, (hex"")),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testEcmulPrecompileParity() public {
        bytes memory input = abi.encodePacked(bytes32(uint256(1)), bytes32(uint256(2)), bytes32(uint256(2)));
        (bool ok, bytes memory expected) = address(7).staticcall(input);
        require(ok && expected.length == 64, "ecmul precompile failed");

        string[] memory ecmuls = new string[](1);
        ecmuls[0] = ecmulArg(input, expected);
        runCaseWithEcmuls(
            "ecmul-precompile",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.ecmulPrecompile, (input)),
            ecmuls
        );
    }

    function testEcmulPrecompileOutOfGasParity() public {
        runCase(
            "ecmul-precompile-oog",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.ecmulPrecompileWithGas, (hex"", uint256(5999))),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testEcmulInvalidPointParity() public {
        bytes memory input = abi.encodePacked(bytes32(uint256(1)), bytes32(uint256(1)), bytes32(uint256(1)));
        string[] memory failures = new string[](1);
        failures[0] = hexString(input);
        runCaseWithBn254Failures(
            "ecmul-invalid-point",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.ecmulPrecompile, (input)),
            new string[](0),
            failures,
            new string[](0)
        );
    }

    function testEcpairingEmptyInputParity() public {
        runCase(
            "ecpairing-empty-input",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.ecpairingPrecompile, (hex"")),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testEcpairingInvalidLengthParity() public {
        runCase(
            "ecpairing-invalid-length",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.ecpairingPrecompile, (hex"00")),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testEcpairingInvalidPointParity() public {
        bytes memory input = abi.encodePacked(
            bytes32(uint256(1)),
            bytes32(uint256(1)),
            bytes32(uint256(0)),
            bytes32(uint256(0)),
            bytes32(uint256(0)),
            bytes32(uint256(0))
        );
        string[] memory failures = new string[](1);
        failures[0] = hexString(input);
        runCaseWithBn254Failures(
            "ecpairing-invalid-point",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.ecpairingPrecompile, (input)),
            new string[](0),
            new string[](0),
            failures
        );
    }

    function testEcpairingPrecompileOutOfGasParity() public {
        runCase(
            "ecpairing-precompile-oog",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.ecpairingPrecompileWithGas, (hex"", uint256(44999))),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testBlake2fPrecompileParity() public {
        bytes memory input = blake2fInput(bytes1(0x01));
        (bool ok, bytes memory expected) = address(9).staticcall(input);
        require(ok && expected.length == 64, "blake2f precompile failed");

        string[] memory blake2fs = new string[](1);
        blake2fs[0] = blake2fArg(input, expected);
        runCaseWithBlake2fs(
            "blake2f-precompile",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.blake2fPrecompile, (input)),
            blake2fs
        );
    }

    function testBlake2fPrecompileOutOfGasParity() public {
        bytes memory input = blake2fInput(bytes1(0x01));
        runCase(
            "blake2f-precompile-oog",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.blake2fPrecompileWithGas, (input, uint256(11))),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testBlake2fInvalidFinalFlagParity() public {
        bytes memory input = blake2fInput(bytes1(0x02));
        runCase(
            "blake2f-invalid-final-flag",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.blake2fPrecompile, (input)),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testBlake2fInvalidLengthParity() public {
        bytes memory input = hex"0000000c";
        runCase(
            "blake2f-invalid-length",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.blake2fPrecompile, (input)),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testPointEvaluationInvalidLengthParity() public {
        runCase(
            "point-evaluation-invalid-length",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.pointEvaluationPrecompile, (hex"00")),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testPointEvaluationInvalidProofParity() public {
        bytes memory input = new bytes(192);
        string[] memory failures = new string[](1);
        failures[0] = hexString(input);
        runCaseWithPointEvaluationFailures(
            "point-evaluation-invalid-proof",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.pointEvaluationPrecompile, (input)),
            failures
        );
    }

    function testPointEvaluationPrecompileOutOfGasParity() public {
        bytes memory input = new bytes(192);
        runCase(
            "point-evaluation-precompile-oog",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.pointEvaluationPrecompileWithGas, (input, uint256(49999))),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testP256VerifyPrecompileParity() public {
        bytes memory input = p256ValidInput();
        (bool ok, bytes memory expected) = address(0x100).staticcall(input);
        require(ok && expected.length == 32, "p256 verify precompile failed");
        require(abi.decode(expected, (bytes32)) == bytes32(uint256(1)), "p256 verify unexpected output");

        string[] memory p256VerifyProofs = new string[](1);
        p256VerifyProofs[0] = hexString(input);
        runCaseWithP256VerifyOracles(
            "p256-verify-precompile",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.p256VerifyPrecompile, (input)),
            p256VerifyProofs,
            new string[](0)
        );
    }

    function testP256VerifyInvalidLengthParity() public {
        runCase(
            "p256-verify-invalid-length",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.p256VerifyPrecompile, (hex"00")),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testP256VerifyInvalidLengthCallValueCommitParity() public {
        runCaseWithState(
            "p256-verify-invalid-length-call-value-commit",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.precompileAtWithValue, (address(0x100), hex"00", uint256(123))),
            500,
            0,
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testP256VerifyInvalidSignatureParity() public {
        bytes memory input = p256InvalidSignatureInput();
        (bool ok, bytes memory expected) = address(0x100).staticcall(input);
        require(ok && expected.length == 0, "p256 verify invalid signature shape changed");

        string[] memory p256VerifyFailures = new string[](1);
        p256VerifyFailures[0] = hexString(input);
        runCaseWithP256VerifyOracles(
            "p256-verify-invalid-signature",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.p256VerifyPrecompile, (input)),
            new string[](0),
            p256VerifyFailures
        );
    }

    function testP256VerifyPrecompileOutOfGasParity() public {
        bytes memory input = p256ValidInput();
        runCase(
            "p256-verify-precompile-oog",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.p256VerifyPrecompileWithGas, (input, uint256(6899))),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testBlsG1AddPrecompileParity() public {
        runBlsSuccessCase("bls-g1add-precompile", address(0x0b), new bytes(256), "--bls-g1add", 128);
    }

    function testBlsG1MsmPrecompileParity() public {
        runBlsSuccessCase("bls-g1msm-precompile", address(0x0c), blsMsmInput(128), "--bls-g1msm", 128);
    }

    function testBlsG1MsmTwoPointDiscountParity() public {
        bytes memory input = abi.encodePacked(blsMsmInput(128), blsMsmInput(128));
        runBlsSuccessCase("bls-g1msm-two-point-discount", address(0x0c), input, "--bls-g1msm", 128);
    }

    function testBlsG2AddPrecompileParity() public {
        runBlsSuccessCase("bls-g2add-precompile", address(0x0d), new bytes(512), "--bls-g2add", 256);
    }

    function testBlsG2MsmPrecompileParity() public {
        runBlsSuccessCase("bls-g2msm-precompile", address(0x0e), blsMsmInput(256), "--bls-g2msm", 256);
    }

    function testBlsPairingPrecompileParity() public {
        runBlsSuccessCase("bls-pairing-precompile", address(0x0f), new bytes(384), "--bls-pairing", 32);
    }

    function testBlsPairingTwoPairGasParity() public {
        runBlsSuccessCase("bls-pairing-two-pair-gas", address(0x0f), new bytes(768), "--bls-pairing", 32);
    }

    function testBlsMapFpToG1PrecompileParity() public {
        runBlsSuccessCase("bls-map-fp-to-g1-precompile", address(0x10), new bytes(64), "--bls-map-fp-to-g1", 128);
    }

    function testBlsMapFp2ToG2PrecompileParity() public {
        runBlsSuccessCase("bls-map-fp2-to-g2-precompile", address(0x11), new bytes(128), "--bls-map-fp2-to-g2", 256);
    }

    function testBlsG1AddInvalidLengthParity() public {
        runBlsCase("bls-g1add-invalid-length", address(0x0b), hex"00");
    }

    function testBlsG1AddInvalidLengthCallValueRollbackParity() public {
        runCaseWithState(
            "bls-g1add-invalid-length-call-value-rollback",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(
                PrecompileParitySubject.precompileAtWithValueAndGas, (address(0x0b), hex"00", uint256(123), 100000)
            ),
            500,
            0,
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testBlsG2AddInvalidLengthParity() public {
        runBlsCase("bls-g2add-invalid-length", address(0x0d), hex"00");
    }

    function testBlsG1MsmEmptyInputParity() public {
        runBlsCase("bls-g1msm-empty-input", address(0x0c), hex"");
    }

    function testBlsG1MsmInvalidLengthParity() public {
        runBlsCase("bls-g1msm-invalid-length", address(0x0c), hex"00");
    }

    function testBlsG2MsmEmptyInputParity() public {
        runBlsCase("bls-g2msm-empty-input", address(0x0e), hex"");
    }

    function testBlsPairingInvalidLengthParity() public {
        runBlsCase("bls-pairing-invalid-length", address(0x0f), hex"00");
    }

    function testBlsPairingEmptyInputParity() public {
        runBlsCase("bls-pairing-empty-input", address(0x0f), hex"");
    }

    function testBlsMapFpToG1InvalidEncodingParity() public {
        bytes memory input = filledBytes(64, 0xff);
        runBlsFailureCase("bls-map-fp-to-g1-invalid-encoding", address(0x10), input, "--bls-map-fp-to-g1-fail", 100000);
    }

    function testBlsMapFp2ToG2InvalidEncodingParity() public {
        bytes memory input = filledBytes(128, 0xff);
        runBlsFailureCase(
            "bls-map-fp2-to-g2-invalid-encoding", address(0x11), input, "--bls-map-fp2-to-g2-fail", 100000
        );
    }

    function testBlsG1AddPrecompileOutOfGasParity() public {
        runBlsOutOfGasCase("bls-g1add-precompile-oog", address(0x0b), new bytes(256), 374);
    }

    function testBlsPairingPrecompileOutOfGasParity() public {
        runBlsOutOfGasCase("bls-pairing-precompile-oog", address(0x0f), new bytes(384), 70299);
    }

    function testEcrecoverPrecompileParity() public {
        uint256 privateKey = 0xBEEF;
        bytes32 digest = 0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef;
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(privateKey, digest);
        address signer = vm.addr(privateKey);

        string[] memory cheatAddresses = new string[](1);
        cheatAddresses[0] = string.concat(uintToString(privateKey), "=", addressArg(signer));
        string[] memory cheatSignatures = new string[](1);
        cheatSignatures[0] = string.concat(
            uintToString(privateKey), ":", wordHex(digest), "=", uintToString(v), ":", wordHex(r), ":", wordHex(s)
        );

        runCaseWithCheatcodeOracles(
            "ecrecover-precompile",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.ecrecoverPrecompile, (digest, v, r, s)),
            cheatAddresses,
            cheatSignatures
        );
    }

    function testEcrecoverPrecompileOutOfGasParity() public {
        runCase(
            "ecrecover-precompile-oog",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(
                PrecompileParitySubject.ecrecoverPrecompileWithGas,
                (bytes32(uint256(0x1234)), uint8(27), bytes32(uint256(0)), bytes32(uint256(0)), uint256(2999))
            ),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testEcrecoverInvalidSignatureParity() public {
        runCase(
            "ecrecover-invalid-signature",
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(
                PrecompileParitySubject.ecrecoverPrecompile,
                (bytes32(uint256(0x1234)), uint8(27), bytes32(uint256(0)), bytes32(uint256(0)))
            ),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function testDynamicCreateParity() public {
        bytes memory data = abi.encodeCall(CreateParityFactory.deployCreate, (777, 11, 4, 3));
        installRuntime(type(CreateParityFactory).runtimeCode);
        vm.deal(TARGET, 5000);

        uint64 nonce = vm.getNonce(TARGET);
        bytes memory preimage = createAddressPreimage(TARGET, nonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));

        string[] memory keccaks = new string[](1);
        keccaks[0] = keccakArg(preimage, keccak256(preimage));
        runDynamicCreateCase(
            DynamicCreateCase({
                name: "dynamic-create",
                data: data,
                rootInitialBalance: 5000,
                rootNonce: nonce,
                expectedCreated: expectedCreated,
                keccakAssignments: keccaks
            })
        );
    }

    function testDynamicCreate2Parity() public {
        bytes32 salt = bytes32(uint256(0xabc123));
        uint256 seed = 17;
        bytes memory data = abi.encodeCall(CreateParityFactory.deployCreate2, (salt, 999, seed, 5, 4));
        bytes memory initCode = abi.encodePacked(type(CreatedParitySubject).creationCode, abi.encode(seed));
        bytes32 initHash = keccak256(initCode);

        installRuntime(type(CreateParityFactory).runtimeCode);
        vm.deal(TARGET, 7000);

        uint64 nonce = vm.getNonce(TARGET);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));

        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));
        runDynamicCreateCase(
            DynamicCreateCase({
                name: "dynamic-create2",
                data: data,
                rootInitialBalance: 7000,
                rootNonce: nonce,
                expectedCreated: expectedCreated,
                keccakAssignments: keccaks
            })
        );
    }

    function testDynamicCreate2CollisionParity() public {
        bytes32 salt = bytes32(uint256(0xfeed42));
        bytes memory initCode = hex"60006000f3";
        bytes32 initHash = keccak256(initCode);
        bytes memory preimage = create2AddressPreimage(TARGET, salt, initHash);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));

        installRuntime(type(CreateParityFactory).runtimeCode);
        vm.etch(expectedCreated, hex"00");

        string[] memory keccaks = new string[](2);
        keccaks[0] = keccakArg(initCode, initHash);
        keccaks[1] = keccakArg(preimage, keccak256(preimage));
        runCreate2CollisionCase(
            "dynamic-create2-collision",
            abi.encodeCall(CreateParityFactory.tryCreate2, (salt, initCode)),
            vm.getNonce(TARGET),
            expectedCreated,
            initCode,
            keccaks
        );
    }

    function runCase(
        string memory name,
        bytes memory code,
        bytes memory data,
        bytes32[] memory initialSlotValues,
        bytes32[] memory checkedSlots
    ) internal {
        runCaseWithState(name, code, data, 0, 0, initialSlotValues, checkedSlots);
    }

    function runCaseWithState(
        string memory name,
        bytes memory code,
        bytes memory data,
        uint256 initialBalance,
        uint256 callValue,
        bytes32[] memory initialSlotValues,
        bytes32[] memory checkedSlots
    ) internal {
        runCaseWithStateAndGasPolicy(
            name, code, data, initialBalance, callValue, initialSlotValues, checkedSlots, false
        );
    }

    function runCaseSkippingGas(
        string memory name,
        bytes memory code,
        bytes memory data,
        bytes32[] memory initialSlotValues,
        bytes32[] memory checkedSlots
    ) internal {
        runCaseWithStateAndGasPolicy(name, code, data, 0, 0, initialSlotValues, checkedSlots, true);
    }

    function runCaseWithStateAndGasPolicy(
        string memory name,
        bytes memory code,
        bytes memory data,
        uint256 initialBalance,
        uint256 callValue,
        bytes32[] memory initialSlotValues,
        bytes32[] memory checkedSlots,
        bool skipGas
    ) internal {
        address target = installRuntime(code);
        vm.deal(target, initialBalance);
        for (uint256 i = 0; i < initialSlotValues.length; i++) {
            vm.store(target, bytes32(i), initialSlotValues[i]);
            vm.coolSlot(target, bytes32(i));
        }

        vm.recordLogs();
        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT, value: callValue}(data);
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command = new string[](
            43 + (skipGas ? 1 : 0) + 4 * initialSlotValues.length + 2 * checkedSlots.length + 2 * logs.length
        );
        command[0] = "python3";
        command[1] = "../../bin/evm_parity.py";
        command[2] = "check";
        command[3] = "--case";
        command[4] = name;
        command[5] = "--code";
        command[6] = hexString(code);
        command[7] = "--calldata";
        command[8] = hexString(data);
        command[9] = "--gas";
        command[10] = uintToString(gas.gasLimit);
        command[11] = "--success";
        command[12] = success ? "1" : "0";
        command[13] = "--output";
        command[14] = hexString(output);
        command[15] = "--gas-used";
        command[16] = uintToString(gas.gasTotalUsed);
        command[17] = "--gas-remaining";
        command[18] = uintToString(gas.gasRemaining);
        command[19] = "--gas-refunded";
        command[20] = intToString(gas.gasRefunded);
        command[21] = "--caller";
        command[22] = hexString(abi.encodePacked(address(this)));
        command[23] = "--origin";
        command[24] = hexString(abi.encodePacked(tx.origin));
        command[25] = "--callvalue";
        command[26] = uintToString(callValue);
        command[27] = "--balance";
        command[28] = uintToString(initialBalance + callValue);
        command[29] = "--expect-balance";
        command[30] = uintToString(target.balance);
        command[31] = "--coinbase";
        command[32] = addressArg(block.coinbase);
        command[33] = "--timestamp";
        command[34] = uintToString(block.timestamp);
        command[35] = "--number";
        command[36] = uintToString(block.number);
        command[37] = "--block-gas-limit";
        command[38] = uintToString(block.gaslimit);
        command[39] = "--basefee";
        command[40] = uintToString(block.basefee);
        command[41] = "--chainid";
        command[42] = uintToString(block.chainid);

        uint256 cursor = 43;
        if (skipGas) {
            command[cursor++] = "--skip-gas";
        }
        for (uint256 i = 0; i < initialSlotValues.length; i++) {
            command[cursor++] = "--storage";
            command[cursor++] = string.concat(wordHex(bytes32(i)), "=", wordHex(initialSlotValues[i]));
            command[cursor++] = "--original-storage";
            command[cursor++] = string.concat(wordHex(bytes32(i)), "=", wordHex(bytes32(0)));
        }
        for (uint256 i = 0; i < checkedSlots.length; i++) {
            bytes32 slot = checkedSlots[i];
            command[cursor++] = "--expect-storage";
            command[cursor++] = string.concat(wordHex(slot), "=", wordHex(vm.load(target, slot)));
        }
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runCaseWithAccountBalances(
        string memory name,
        bytes memory code,
        bytes memory data,
        string[] memory accountBalanceAssignments,
        address[] memory warmAddresses
    ) internal {
        address target = installRuntime(code);

        vm.recordLogs();
        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(data);
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command =
            new string[](43 + 2 * accountBalanceAssignments.length + 2 * warmAddresses.length + 2 * logs.length);
        BaseCommandCase memory base;
        base.name = name;
        base.code = code;
        base.data = data;
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = 0;
        base.expectedBalance = target.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        for (uint256 i = 0; i < accountBalanceAssignments.length; i++) {
            command[cursor++] = "--account-balance";
            command[cursor++] = accountBalanceAssignments[i];
        }
        for (uint256 i = 0; i < warmAddresses.length; i++) {
            command[cursor++] = "--warm-address";
            command[cursor++] = addressArg(warmAddresses[i]);
        }
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runCaseWithAccountCode(
        string memory name,
        bytes memory code,
        bytes memory data,
        address account,
        bytes memory accountCode
    ) internal {
        vm.etch(account, accountCode);
        address target = installRuntime(code);
        require(account.code.length == accountCode.length, "account code not installed");

        vm.recordLogs();
        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(data);
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command = new string[](49 + 2 * logs.length);
        BaseCommandCase memory base;
        base.name = name;
        base.code = code;
        base.data = data;
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = 0;
        base.expectedBalance = target.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        command[cursor++] = "--account";
        command[cursor++] = string.concat(addressArg(account), "=", hexString(accountCode));
        command[cursor++] = "--warm-address";
        command[cursor++] = addressArg(account);
        command[cursor++] = "--expect-account-code";
        command[cursor++] = string.concat(addressArg(account), "=", hexString(accountCode));
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runCreateRevertCase(string memory name, bytes memory code, bytes memory initCode) internal {
        require(initCode.length == 8, "unexpected initCode length");
        runCreateFailureCase(name, code);
    }

    function runCreateFailureCase(string memory name, bytes memory code) internal {
        runCreateResultCase(name, code, hex"");
    }

    function runCreateResultCase(string memory name, bytes memory code, bytes memory expectedCreatedCode) internal {
        address target = installRuntime(code);
        uint64 rootNonce = vm.getNonce(target);
        bytes memory preimage = createAddressPreimage(target, rootNonce);
        address expectedCreated = address(uint160(uint256(keccak256(preimage))));

        vm.recordLogs();
        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(hex"");
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command = new string[](55 + 2 * logs.length);
        BaseCommandCase memory base;
        base.name = name;
        base.code = code;
        base.data = hex"";
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = 0;
        base.expectedBalance = target.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        command[cursor++] = "--nonce";
        command[cursor++] = uintToString(rootNonce);
        command[cursor++] = "--expect-nonce";
        command[cursor++] = uintToString(vm.getNonce(target));
        command[cursor++] = "--keccak";
        command[cursor++] = keccakArg(preimage, keccak256(preimage));
        command[cursor++] = "--expect-account-balance";
        command[cursor++] = string.concat(addressArg(expectedCreated), "=", uintToString(expectedCreated.balance));
        command[cursor++] = "--expect-account-nonce";
        command[cursor++] = string.concat(addressArg(expectedCreated), "=", uintToString(vm.getNonce(expectedCreated)));
        command[cursor++] = "--expect-account-code";
        command[cursor++] = string.concat(addressArg(expectedCreated), "=", hexString(expectedCreatedCode));
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runCallValueNewAccountCase(string memory name, bytes memory code, uint256 initialBalance) internal {
        address target = installRuntime(code);
        vm.deal(target, initialBalance);

        vm.recordLogs();
        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(hex"");
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command = new string[](49 + 2 * logs.length);
        BaseCommandCase memory base;
        base.name = name;
        base.code = code;
        base.data = hex"";
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = initialBalance;
        base.expectedBalance = target.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        command[cursor++] = "--expect-account-balance";
        command[cursor++] = string.concat(addressArg(WORKER), "=", uintToString(WORKER.balance));
        command[cursor++] = "--expect-account-nonce";
        command[cursor++] = string.concat(addressArg(WORKER), "=", uintToString(vm.getNonce(WORKER)));
        command[cursor++] = "--expect-account-code";
        command[cursor++] = string.concat(addressArg(WORKER), "=0x");
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runCaseWithFeeContext(
        string memory name,
        bytes memory code,
        uint256 gasPrice,
        uint256 prevrandaoValue,
        uint256 blobBaseFee
    ) internal {
        address target = installRuntime(code);

        vm.recordLogs();
        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(hex"");
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command = new string[](49 + 2 * logs.length);
        BaseCommandCase memory base;
        base.name = name;
        base.code = code;
        base.data = hex"";
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = 0;
        base.expectedBalance = target.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        command[cursor++] = "--gasprice";
        command[cursor++] = uintToString(gasPrice);
        command[cursor++] = "--prevrandao";
        command[cursor++] = uintToString(prevrandaoValue);
        command[cursor++] = "--blobbasefee";
        command[cursor++] = uintToString(blobBaseFee);
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runSelfdestructExistingCase(
        string memory name,
        bytes memory code,
        uint256 initialBalance,
        bytes32[] memory initialSlotValues,
        bytes32[] memory checkedSlots
    ) internal {
        vm.etch(WORKER, hex"00");
        address target = installRuntime(code);
        vm.deal(target, initialBalance);
        for (uint256 i = 0; i < initialSlotValues.length; i++) {
            vm.store(target, bytes32(i), initialSlotValues[i]);
            vm.coolSlot(target, bytes32(i));
        }

        vm.recordLogs();
        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(hex"");
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command =
            new string[](51 + 4 * initialSlotValues.length + 2 * checkedSlots.length + 2 * logs.length);
        BaseCommandCase memory base;
        base.name = name;
        base.code = code;
        base.data = hex"";
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = initialBalance;
        base.expectedBalance = target.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        command[cursor++] = "--account";
        command[cursor++] = string.concat(addressArg(WORKER), "=0x00");
        command[cursor++] = "--warm-address";
        command[cursor++] = addressArg(WORKER);
        command[cursor++] = "--expect-account-balance";
        command[cursor++] = string.concat(addressArg(WORKER), "=", uintToString(WORKER.balance));
        command[cursor++] = "--expect-account-code";
        command[cursor++] = string.concat(addressArg(TARGET), "=", hexString(code));
        for (uint256 i = 0; i < initialSlotValues.length; i++) {
            command[cursor++] = "--storage";
            command[cursor++] = string.concat(wordHex(bytes32(i)), "=", wordHex(initialSlotValues[i]));
            command[cursor++] = "--original-storage";
            command[cursor++] = string.concat(wordHex(bytes32(i)), "=", wordHex(bytes32(0)));
        }
        for (uint256 i = 0; i < checkedSlots.length; i++) {
            bytes32 slot = checkedSlots[i];
            command[cursor++] = "--expect-storage";
            command[cursor++] = string.concat(wordHex(slot), "=", wordHex(vm.load(target, slot)));
        }
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runCaseWithBlockhashes(
        string memory name,
        bytes memory code,
        bytes memory data,
        string[] memory blockhashAssignments
    ) internal {
        address target = installRuntime(code);

        vm.recordLogs();
        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(data);
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command = new string[](43 + 2 * blockhashAssignments.length + 2 * logs.length);
        BaseCommandCase memory base;
        base.name = name;
        base.code = code;
        base.data = data;
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = 0;
        base.expectedBalance = target.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        for (uint256 i = 0; i < blockhashAssignments.length; i++) {
            command[cursor++] = "--blockhash";
            command[cursor++] = blockhashAssignments[i];
        }
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runCaseWithBlobhashes(string memory name, bytes memory code, bytes32[] memory blobhashAssignments)
        internal
    {
        address target = installRuntime(code);

        vm.recordLogs();
        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(hex"");
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command = new string[](43 + 2 * blobhashAssignments.length + 2 * logs.length);
        BaseCommandCase memory base;
        base.name = name;
        base.code = code;
        base.data = hex"";
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = 0;
        base.expectedBalance = target.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        for (uint256 i = 0; i < blobhashAssignments.length; i++) {
            command[cursor++] = "--blobhash";
            command[cursor++] = wordHex(blobhashAssignments[i]);
        }
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runCaseWithKeccaks(
        string memory name,
        bytes memory code,
        bytes memory data,
        string[] memory keccakAssignments
    ) internal {
        address target = installRuntime(code);

        vm.recordLogs();
        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(data);
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command = new string[](43 + 2 * keccakAssignments.length + 2 * logs.length);
        BaseCommandCase memory base;
        base.name = name;
        base.code = code;
        base.data = data;
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = 0;
        base.expectedBalance = target.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        for (uint256 i = 0; i < keccakAssignments.length; i++) {
            command[cursor++] = "--keccak";
            command[cursor++] = keccakAssignments[i];
        }
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runCaseWithSha256s(
        string memory name,
        bytes memory code,
        bytes memory data,
        string[] memory sha256Assignments
    ) internal {
        address target = installRuntime(code);

        vm.recordLogs();
        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(data);
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command = new string[](43 + 2 * sha256Assignments.length + 2 * logs.length);
        BaseCommandCase memory base;
        base.name = name;
        base.code = code;
        base.data = data;
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = 0;
        base.expectedBalance = target.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        for (uint256 i = 0; i < sha256Assignments.length; i++) {
            command[cursor++] = "--sha256";
            command[cursor++] = sha256Assignments[i];
        }
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runCaseWithRipemd160s(
        string memory name,
        bytes memory code,
        bytes memory data,
        string[] memory ripemd160Assignments
    ) internal {
        address target = installRuntime(code);

        vm.recordLogs();
        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(data);
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command = new string[](43 + 2 * ripemd160Assignments.length + 2 * logs.length);
        BaseCommandCase memory base;
        base.name = name;
        base.code = code;
        base.data = data;
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = 0;
        base.expectedBalance = target.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        for (uint256 i = 0; i < ripemd160Assignments.length; i++) {
            command[cursor++] = "--ripemd160";
            command[cursor++] = ripemd160Assignments[i];
        }
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runCaseWithModexps(
        string memory name,
        bytes memory code,
        bytes memory data,
        string[] memory modexpAssignments
    ) internal {
        address target = installRuntime(code);

        vm.recordLogs();
        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(data);
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command = new string[](43 + 2 * modexpAssignments.length + 2 * logs.length);
        BaseCommandCase memory base;
        base.name = name;
        base.code = code;
        base.data = data;
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = 0;
        base.expectedBalance = target.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        for (uint256 i = 0; i < modexpAssignments.length; i++) {
            command[cursor++] = "--modexp";
            command[cursor++] = modexpAssignments[i];
        }
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runCaseWithEcadds(
        string memory name,
        bytes memory code,
        bytes memory data,
        string[] memory ecaddAssignments
    ) internal {
        address target = installRuntime(code);

        vm.recordLogs();
        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(data);
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command = new string[](43 + 2 * ecaddAssignments.length + 2 * logs.length);
        BaseCommandCase memory base;
        base.name = name;
        base.code = code;
        base.data = data;
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = 0;
        base.expectedBalance = target.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        for (uint256 i = 0; i < ecaddAssignments.length; i++) {
            command[cursor++] = "--ecadd";
            command[cursor++] = ecaddAssignments[i];
        }
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runCaseWithEcmuls(
        string memory name,
        bytes memory code,
        bytes memory data,
        string[] memory ecmulAssignments
    ) internal {
        address target = installRuntime(code);

        vm.recordLogs();
        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(data);
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command = new string[](43 + 2 * ecmulAssignments.length + 2 * logs.length);
        BaseCommandCase memory base;
        base.name = name;
        base.code = code;
        base.data = data;
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = 0;
        base.expectedBalance = target.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        for (uint256 i = 0; i < ecmulAssignments.length; i++) {
            command[cursor++] = "--ecmul";
            command[cursor++] = ecmulAssignments[i];
        }
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runCaseWithEcpairings(
        string memory name,
        bytes memory code,
        bytes memory data,
        string[] memory ecpairingAssignments
    ) internal {
        address target = installRuntime(code);

        vm.recordLogs();
        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(data);
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command = new string[](43 + 2 * ecpairingAssignments.length + 2 * logs.length);
        BaseCommandCase memory base;
        base.name = name;
        base.code = code;
        base.data = data;
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = 0;
        base.expectedBalance = target.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        for (uint256 i = 0; i < ecpairingAssignments.length; i++) {
            command[cursor++] = "--ecpairing";
            command[cursor++] = ecpairingAssignments[i];
        }
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runCaseWithBn254Failures(
        string memory name,
        bytes memory code,
        bytes memory data,
        string[] memory ecaddFailures,
        string[] memory ecmulFailures,
        string[] memory ecpairingFailures
    ) internal {
        address target = installRuntime(code);

        vm.recordLogs();
        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(data);
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command = new string[](
            43 + 2 * ecaddFailures.length + 2 * ecmulFailures.length + 2 * ecpairingFailures.length + 2 * logs.length
        );
        BaseCommandCase memory base;
        base.name = name;
        base.code = code;
        base.data = data;
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = 0;
        base.expectedBalance = target.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        for (uint256 i = 0; i < ecaddFailures.length; i++) {
            command[cursor++] = "--ecadd-fail";
            command[cursor++] = ecaddFailures[i];
        }
        for (uint256 i = 0; i < ecmulFailures.length; i++) {
            command[cursor++] = "--ecmul-fail";
            command[cursor++] = ecmulFailures[i];
        }
        for (uint256 i = 0; i < ecpairingFailures.length; i++) {
            command[cursor++] = "--ecpairing-fail";
            command[cursor++] = ecpairingFailures[i];
        }
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runCaseWithPointEvaluationFailures(
        string memory name,
        bytes memory code,
        bytes memory data,
        string[] memory pointEvaluationFailures
    ) internal {
        address target = installRuntime(code);

        vm.recordLogs();
        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(data);
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command = new string[](43 + 2 * pointEvaluationFailures.length + 2 * logs.length);
        BaseCommandCase memory base;
        base.name = name;
        base.code = code;
        base.data = data;
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = 0;
        base.expectedBalance = target.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        for (uint256 i = 0; i < pointEvaluationFailures.length; i++) {
            command[cursor++] = "--point-evaluation-fail";
            command[cursor++] = pointEvaluationFailures[i];
        }
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runCaseWithExtraArgs(string memory name, bytes memory code, bytes memory data, string[] memory extraArgs)
        internal
    {
        address target = installRuntime(code);

        vm.recordLogs();
        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(data);
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command = new string[](43 + extraArgs.length + 2 * logs.length);
        BaseCommandCase memory base;
        base.name = name;
        base.code = code;
        base.data = data;
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = 0;
        base.expectedBalance = target.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        for (uint256 i = 0; i < extraArgs.length; i++) {
            command[cursor++] = extraArgs[i];
        }
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runCaseWithP256VerifyOracles(
        string memory name,
        bytes memory code,
        bytes memory data,
        string[] memory p256VerifyProofs,
        string[] memory p256VerifyFailures
    ) internal {
        address target = installRuntime(code);

        vm.recordLogs();
        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(data);
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command =
            new string[](43 + 2 * p256VerifyProofs.length + 2 * p256VerifyFailures.length + 2 * logs.length);
        BaseCommandCase memory base;
        base.name = name;
        base.code = code;
        base.data = data;
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = 0;
        base.expectedBalance = target.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        for (uint256 i = 0; i < p256VerifyProofs.length; i++) {
            command[cursor++] = "--p256-verify";
            command[cursor++] = p256VerifyProofs[i];
        }
        for (uint256 i = 0; i < p256VerifyFailures.length; i++) {
            command[cursor++] = "--p256-verify-fail";
            command[cursor++] = p256VerifyFailures[i];
        }
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runCaseWithBlake2fs(
        string memory name,
        bytes memory code,
        bytes memory data,
        string[] memory blake2fAssignments
    ) internal {
        address target = installRuntime(code);

        vm.recordLogs();
        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(data);
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command = new string[](43 + 2 * blake2fAssignments.length + 2 * logs.length);
        BaseCommandCase memory base;
        base.name = name;
        base.code = code;
        base.data = data;
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = 0;
        base.expectedBalance = target.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        for (uint256 i = 0; i < blake2fAssignments.length; i++) {
            command[cursor++] = "--blake2f";
            command[cursor++] = blake2fAssignments[i];
        }
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runCaseWithCheatcodeOracles(
        string memory name,
        bytes memory code,
        bytes memory data,
        string[] memory cheatAddressAssignments,
        string[] memory cheatSignatureAssignments
    ) internal {
        address target = installRuntime(code);

        vm.recordLogs();
        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(data);
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        string[] memory command = new string[](
            43 + 2 * cheatAddressAssignments.length + 2 * cheatSignatureAssignments.length + 2 * logs.length
        );
        BaseCommandCase memory base;
        base.name = name;
        base.code = code;
        base.data = data;
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = 0;
        base.expectedBalance = target.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        for (uint256 i = 0; i < cheatAddressAssignments.length; i++) {
            command[cursor++] = "--cheat-addr";
            command[cursor++] = cheatAddressAssignments[i];
        }
        for (uint256 i = 0; i < cheatSignatureAssignments.length; i++) {
            command[cursor++] = "--cheat-sign";
            command[cursor++] = cheatSignatureAssignments[i];
        }
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runMultiCase(
        string memory name,
        bytes memory data,
        bytes32[] memory rootInitialSlotValues,
        bytes32[] memory rootCheckedSlots,
        bytes32[] memory workerInitialSlotValues,
        bytes32[] memory workerCheckedSlots
    ) internal {
        installRuntime(type(MultiCallerParitySubject).runtimeCode);
        vm.etch(WORKER, type(WorkerParitySubject).runtimeCode);
        vm.etch(DELEGATE_LIB, type(DelegateParityLib).runtimeCode);

        for (uint256 i = 0; i < rootInitialSlotValues.length; i++) {
            vm.store(TARGET, bytes32(i), rootInitialSlotValues[i]);
            vm.coolSlot(TARGET, bytes32(i));
        }
        for (uint256 i = 0; i < workerInitialSlotValues.length; i++) {
            vm.store(WORKER, bytes32(i), workerInitialSlotValues[i]);
            vm.coolSlot(WORKER, bytes32(i));
        }

        vm.recordLogs();
        (bool success, bytes memory output) = TARGET.call{gas: GAS_LIMIT}(data);
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        uint256 commandLength = 55 + 4 * rootInitialSlotValues.length + 2 * rootCheckedSlots.length + 4
            * workerInitialSlotValues.length + 2 * workerCheckedSlots.length + 2 * logs.length;
        string[] memory command = new string[](commandLength);
        uint256 cursor = fillBaseCommand(
            command,
            name,
            type(MultiCallerParitySubject).runtimeCode,
            data,
            success,
            output,
            gas,
            0,
            TARGET.balance + WORKER.balance,
            TARGET.balance
        );

        command[cursor++] = "--account";
        command[cursor++] = string.concat(addressArg(WORKER), "=", hexString(type(WorkerParitySubject).runtimeCode));
        command[cursor++] = "--account";
        command[cursor++] = string.concat(addressArg(DELEGATE_LIB), "=", hexString(type(DelegateParityLib).runtimeCode));
        command[cursor++] = "--warm-address";
        command[cursor++] = addressArg(WORKER);
        command[cursor++] = "--warm-address";
        command[cursor++] = addressArg(DELEGATE_LIB);
        command[cursor++] = "--account-balance";
        command[cursor++] = string.concat(addressArg(WORKER), "=0");
        command[cursor++] = "--expect-account-balance";
        command[cursor++] = string.concat(addressArg(WORKER), "=", uintToString(WORKER.balance));

        for (uint256 i = 0; i < rootInitialSlotValues.length; i++) {
            command[cursor++] = "--storage";
            command[cursor++] = string.concat(wordHex(bytes32(i)), "=", wordHex(rootInitialSlotValues[i]));
            command[cursor++] = "--original-storage";
            command[cursor++] = string.concat(wordHex(bytes32(i)), "=", wordHex(bytes32(0)));
        }
        for (uint256 i = 0; i < rootCheckedSlots.length; i++) {
            bytes32 slot = rootCheckedSlots[i];
            command[cursor++] = "--expect-storage";
            command[cursor++] = string.concat(wordHex(slot), "=", wordHex(vm.load(TARGET, slot)));
        }
        for (uint256 i = 0; i < workerInitialSlotValues.length; i++) {
            command[cursor++] = "--account-storage";
            command[cursor++] =
                string.concat(addressArg(WORKER), ":", wordHex(bytes32(i)), "=", wordHex(workerInitialSlotValues[i]));
            command[cursor++] = "--account-original-storage";
            command[cursor++] = string.concat(addressArg(WORKER), ":", wordHex(bytes32(i)), "=", wordHex(bytes32(0)));
        }
        for (uint256 i = 0; i < workerCheckedSlots.length; i++) {
            bytes32 slot = workerCheckedSlots[i];
            command[cursor++] = "--expect-account-storage";
            command[cursor++] =
                string.concat(addressArg(WORKER), ":", wordHex(slot), "=", wordHex(vm.load(WORKER, slot)));
        }
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runDynamicCreateCase(DynamicCreateCase memory createCase) internal {
        vm.recordLogs();
        (bool success, bytes memory output) = TARGET.call{gas: GAS_LIMIT}(createCase.data);
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        uint256 commandLength = 57 + 2 * createCase.keccakAssignments.length + 2 * logs.length;
        string[] memory command = new string[](commandLength);

        BaseCommandCase memory base;
        base.name = createCase.name;
        base.code = type(CreateParityFactory).runtimeCode;
        base.data = createCase.data;
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = createCase.rootInitialBalance;
        base.expectedBalance = TARGET.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        command[cursor++] = "--nonce";
        command[cursor++] = uintToString(createCase.rootNonce);
        command[cursor++] = "--expect-nonce";
        command[cursor++] = uintToString(vm.getNonce(TARGET));
        for (uint256 i = 0; i < createCase.keccakAssignments.length; i++) {
            command[cursor++] = "--keccak";
            command[cursor++] = createCase.keccakAssignments[i];
        }
        command[cursor++] = "--expect-storage";
        command[cursor++] = string.concat(wordHex(bytes32(uint256(0))), "=", wordHex(vm.load(TARGET, bytes32(0))));
        command[cursor++] = "--expect-storage";
        command[cursor++] =
            string.concat(wordHex(bytes32(uint256(1))), "=", wordHex(vm.load(TARGET, bytes32(uint256(1)))));
        command[cursor++] = "--expect-account-storage";
        command[cursor++] = string.concat(
            addressArg(createCase.expectedCreated),
            ":",
            wordHex(bytes32(0)),
            "=",
            wordHex(vm.load(createCase.expectedCreated, bytes32(0)))
        );
        command[cursor++] = "--expect-account-balance";
        command[cursor++] = string.concat(
            addressArg(createCase.expectedCreated), "=", uintToString(createCase.expectedCreated.balance)
        );
        command[cursor++] = "--expect-account-nonce";
        command[cursor++] = string.concat(
            addressArg(createCase.expectedCreated), "=", uintToString(vm.getNonce(createCase.expectedCreated))
        );
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function runCreate2CollisionCase(
        string memory name,
        bytes memory data,
        uint256 rootNonce,
        address expectedCreated,
        bytes memory collisionCode,
        string[] memory keccakAssignments
    ) internal {
        vm.recordLogs();
        (bool success, bytes memory output) = TARGET.call{gas: GAS_LIMIT}(data);
        Vm.Gas memory gas = vm.lastCallGas();
        Vm.Log[] memory logs = vm.getRecordedLogs();

        uint256 commandLength = 59 + 2 * keccakAssignments.length + 2 * logs.length;
        string[] memory command = new string[](commandLength);

        BaseCommandCase memory base;
        base.name = name;
        base.code = type(CreateParityFactory).runtimeCode;
        base.data = data;
        base.success = success;
        base.output = output;
        base.gas = gas;
        base.callValue = 0;
        base.initialBalance = 0;
        base.expectedBalance = TARGET.balance;
        uint256 cursor = fillBaseCommandStruct(command, base);

        command[cursor++] = "--nonce";
        command[cursor++] = uintToString(rootNonce);
        command[cursor++] = "--expect-nonce";
        command[cursor++] = uintToString(vm.getNonce(TARGET));
        command[cursor++] = "--account";
        command[cursor++] = string.concat(addressArg(expectedCreated), "=", hexString(collisionCode));
        command[cursor++] = "--expect-account-balance";
        command[cursor++] = string.concat(addressArg(expectedCreated), "=", uintToString(expectedCreated.balance));
        command[cursor++] = "--expect-account-nonce";
        command[cursor++] = string.concat(addressArg(expectedCreated), "=", uintToString(vm.getNonce(expectedCreated)));
        command[cursor++] = "--expect-account-code";
        command[cursor++] = string.concat(addressArg(expectedCreated), "=", hexString(collisionCode));
        for (uint256 i = 0; i < keccakAssignments.length; i++) {
            command[cursor++] = "--keccak";
            command[cursor++] = keccakAssignments[i];
        }
        command[cursor++] = "--expect-storage";
        command[cursor++] = string.concat(wordHex(bytes32(uint256(0))), "=", wordHex(vm.load(TARGET, bytes32(0))));
        command[cursor++] = "--expect-storage";
        command[cursor++] =
            string.concat(wordHex(bytes32(uint256(1))), "=", wordHex(vm.load(TARGET, bytes32(uint256(1)))));
        for (uint256 i = 0; i < logs.length; i++) {
            command[cursor++] = "--expect-log";
            command[cursor++] = logSpec(logs[i]);
        }

        vm.ffi(command);
    }

    function fillBaseCommandStruct(string[] memory command, BaseCommandCase memory base)
        internal
        view
        returns (uint256 cursor)
    {
        command[0] = "python3";
        command[1] = "../../bin/evm_parity.py";
        command[2] = "check";
        command[3] = "--case";
        command[4] = base.name;
        command[5] = "--code";
        command[6] = hexString(base.code);
        command[7] = "--calldata";
        command[8] = hexString(base.data);
        command[9] = "--gas";
        command[10] = uintToString(base.gas.gasLimit);
        command[11] = "--success";
        command[12] = base.success ? "1" : "0";
        command[13] = "--output";
        command[14] = hexString(base.output);
        command[15] = "--gas-used";
        command[16] = uintToString(base.gas.gasTotalUsed);
        command[17] = "--gas-remaining";
        command[18] = uintToString(base.gas.gasRemaining);
        command[19] = "--gas-refunded";
        command[20] = intToString(base.gas.gasRefunded);
        command[21] = "--caller";
        command[22] = hexString(abi.encodePacked(address(this)));
        command[23] = "--origin";
        command[24] = hexString(abi.encodePacked(tx.origin));
        command[25] = "--callvalue";
        command[26] = uintToString(base.callValue);
        command[27] = "--balance";
        command[28] = uintToString(base.initialBalance + base.callValue);
        command[29] = "--expect-balance";
        command[30] = uintToString(base.expectedBalance);
        command[31] = "--coinbase";
        command[32] = addressArg(block.coinbase);
        command[33] = "--timestamp";
        command[34] = uintToString(block.timestamp);
        command[35] = "--number";
        command[36] = uintToString(block.number);
        command[37] = "--block-gas-limit";
        command[38] = uintToString(block.gaslimit);
        command[39] = "--basefee";
        command[40] = uintToString(block.basefee);
        command[41] = "--chainid";
        command[42] = uintToString(block.chainid);
        return 43;
    }

    function fillBaseCommand(
        string[] memory command,
        string memory name,
        bytes memory code,
        bytes memory data,
        bool success,
        bytes memory output,
        Vm.Gas memory gas,
        uint256 callValue,
        uint256 initialBalance,
        uint256 expectedBalance
    ) internal view returns (uint256 cursor) {
        command[0] = "python3";
        command[1] = "../../bin/evm_parity.py";
        command[2] = "check";
        command[3] = "--case";
        command[4] = name;
        command[5] = "--code";
        command[6] = hexString(code);
        command[7] = "--calldata";
        command[8] = hexString(data);
        command[9] = "--gas";
        command[10] = uintToString(gas.gasLimit);
        command[11] = "--success";
        command[12] = success ? "1" : "0";
        command[13] = "--output";
        command[14] = hexString(output);
        command[15] = "--gas-used";
        command[16] = uintToString(gas.gasTotalUsed);
        command[17] = "--gas-remaining";
        command[18] = uintToString(gas.gasRemaining);
        command[19] = "--gas-refunded";
        command[20] = intToString(gas.gasRefunded);
        command[21] = "--caller";
        command[22] = hexString(abi.encodePacked(address(this)));
        command[23] = "--origin";
        command[24] = hexString(abi.encodePacked(tx.origin));
        command[25] = "--callvalue";
        command[26] = uintToString(callValue);
        command[27] = "--balance";
        command[28] = uintToString(initialBalance + callValue);
        command[29] = "--expect-balance";
        command[30] = uintToString(expectedBalance);
        command[31] = "--coinbase";
        command[32] = addressArg(block.coinbase);
        command[33] = "--timestamp";
        command[34] = uintToString(block.timestamp);
        command[35] = "--number";
        command[36] = uintToString(block.number);
        command[37] = "--block-gas-limit";
        command[38] = uintToString(block.gaslimit);
        command[39] = "--basefee";
        command[40] = uintToString(block.basefee);
        command[41] = "--chainid";
        command[42] = uintToString(block.chainid);
        return 43;
    }

    function installRuntime(bytes memory code) internal returns (address target) {
        vm.etch(TARGET, code);
        return TARGET;
    }

    function createAddressPreimage(address creator, uint256 nonce) internal pure returns (bytes memory) {
        if (nonce == 0) {
            return abi.encodePacked(bytes1(0xd6), bytes1(0x94), creator, bytes1(0x80));
        }
        require(nonce < 0x80, "nonce too large");
        return abi.encodePacked(bytes1(0xd6), bytes1(0x94), creator, bytes1(uint8(nonce)));
    }

    function create2AddressPreimage(address creator, bytes32 salt, bytes32 initHash)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encodePacked(bytes1(0xff), creator, salt, initHash);
    }

    function blake2fInput(bytes1 finalFlag) internal pure returns (bytes memory) {
        return abi.encodePacked(
            hex"0000000c",
            bytes32(0),
            bytes32(0),
            bytes32(0),
            bytes32(0),
            bytes32(0),
            bytes32(0),
            hex"0000000000000000",
            hex"0000000000000000",
            finalFlag
        );
    }

    function blsMsmInput(uint256 pointLength) internal pure returns (bytes memory) {
        return abi.encodePacked(new bytes(pointLength), bytes32(uint256(1)));
    }

    function filledBytes(uint256 length, uint8 value) internal pure returns (bytes memory) {
        bytes memory data = new bytes(length);
        for (uint256 i = 0; i < length; i++) {
            data[i] = bytes1(value);
        }
        return data;
    }

    function runBlsSuccessCase(
        string memory name,
        address precompile,
        bytes memory input,
        string memory oracleFlag,
        uint256 expectedLength
    ) internal {
        (bool ok, bytes memory expected) = precompile.staticcall(input);
        require(ok && expected.length == expectedLength, "bls precompile shape changed");

        string[] memory extraArgs = new string[](2);
        extraArgs[0] = oracleFlag;
        extraArgs[1] = bytesArg(input, expected);
        runCaseWithExtraArgs(
            name,
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.precompileAt, (precompile, input)),
            extraArgs
        );
    }

    function runBlsFailureCase(
        string memory name,
        address precompile,
        bytes memory input,
        string memory failureFlag,
        uint256 gasAmount
    ) internal {
        (bool ok, bytes memory expected) = precompile.staticcall{gas: gasAmount}(input);
        require(!ok && expected.length == 0, "bls failure shape changed");

        string[] memory extraArgs = new string[](2);
        extraArgs[0] = failureFlag;
        extraArgs[1] = hexString(input);
        runCaseWithExtraArgs(
            name,
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.precompileAtWithGas, (precompile, input, gasAmount)),
            extraArgs
        );
    }

    function runBlsCase(string memory name, address precompile, bytes memory input) internal {
        runCase(
            name,
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.precompileAt, (precompile, input)),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function runBlsOutOfGasCase(string memory name, address precompile, bytes memory input, uint256 gasAmount)
        internal
    {
        runCase(
            name,
            type(PrecompileParitySubject).runtimeCode,
            abi.encodeCall(PrecompileParitySubject.precompileAtWithGas, (precompile, input, gasAmount)),
            new bytes32[](0),
            new bytes32[](0)
        );
    }

    function p256ValidInput() internal pure returns (bytes memory) {
        return abi.encodePacked(
            bytes32(0xbb5a52f42f9c9261ed4361f59422a1e30036e7c32b270c8807a419feca605023),
            bytes32(0x2ba3a8be6b94d5ec80a6d9d1190a436effe50d85a1eee859b8cc6af9bd5c2e18),
            bytes32(0x4cd60b855d442f5b3c7b11eb6c4e0ae7525fe710fab9aa7c77a67f79e6fadd76),
            bytes32(0x2927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838),
            bytes32(0xc7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e)
        );
    }

    function p256InvalidSignatureInput() internal pure returns (bytes memory) {
        bytes memory input = p256ValidInput();
        input[95] = bytes1(uint8(input[95]) ^ 0x01);
        return input;
    }

    function keccakArg(bytes memory data, bytes32 hash) internal pure returns (string memory) {
        return string.concat(hexString(data), "=", wordHex(hash));
    }

    function sha256Arg(bytes memory data, bytes32 hash) internal pure returns (string memory) {
        return string.concat(hexString(data), "=", wordHex(hash));
    }

    function ripemd160Arg(bytes memory data, bytes20 hash) internal pure returns (string memory) {
        return string.concat(hexString(data), "=", wordHex(bytes32(uint256(uint160(hash)))));
    }

    function modexpArg(bytes memory data, bytes memory output) internal pure returns (string memory) {
        return string.concat(hexString(data), "=", hexString(output));
    }

    function bytesArg(bytes memory data, bytes memory output) internal pure returns (string memory) {
        return string.concat(hexString(data), "=", hexString(output));
    }

    function ecaddArg(bytes memory data, bytes memory output) internal pure returns (string memory) {
        return string.concat(hexString(data), "=", hexString(output));
    }

    function ecmulArg(bytes memory data, bytes memory output) internal pure returns (string memory) {
        return string.concat(hexString(data), "=", hexString(output));
    }

    function ecpairingArg(bytes memory data, bytes memory output) internal pure returns (string memory) {
        return string.concat(hexString(data), "=", hexString(output));
    }

    function blake2fArg(bytes memory data, bytes memory output) internal pure returns (string memory) {
        return string.concat(hexString(data), "=", hexString(output));
    }

    function hexString(bytes memory data) internal pure returns (string memory) {
        bytes memory alphabet = "0123456789abcdef";
        bytes memory out = new bytes(2 + data.length * 2);
        out[0] = "0";
        out[1] = "x";
        for (uint256 i = 0; i < data.length; i++) {
            out[2 + i * 2] = alphabet[uint8(data[i]) >> 4];
            out[3 + i * 2] = alphabet[uint8(data[i]) & 0x0f];
        }
        return string(out);
    }

    function wordHex(bytes32 value) internal pure returns (string memory) {
        return hexString(abi.encodePacked(value));
    }

    function addressWordHex(address value) internal pure returns (string memory) {
        return wordHex(bytes32(uint256(uint160(value))));
    }

    function addressArg(address value) internal pure returns (string memory) {
        return hexString(abi.encodePacked(value));
    }

    function topicsHex(bytes32[] memory topics) internal pure returns (string memory) {
        if (topics.length == 0) return "";
        string memory out = wordHex(topics[0]);
        for (uint256 i = 1; i < topics.length; i++) {
            out = string.concat(out, ",", wordHex(topics[i]));
        }
        return out;
    }

    function logSpec(Vm.Log memory entry) internal pure returns (string memory) {
        return string.concat(addressWordHex(entry.emitter), "|", topicsHex(entry.topics), "|", hexString(entry.data));
    }

    function uintToString(uint256 value) internal pure returns (string memory) {
        if (value == 0) return "0";
        uint256 temp = value;
        uint256 digits;
        while (temp != 0) {
            digits++;
            temp /= 10;
        }
        bytes memory buffer = new bytes(digits);
        while (value != 0) {
            digits -= 1;
            buffer[digits] = bytes1(uint8(48 + uint256(value % 10)));
            value /= 10;
        }
        return string(buffer);
    }

    function intToString(int256 value) internal pure returns (string memory) {
        if (value >= 0) return uintToString(uint256(value));
        return string.concat("-", uintToString(uint256(-value)));
    }
}
