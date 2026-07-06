// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {
    OpenZeppelinERC20SnapshotHarness
} from "../src/OpenZeppelinERC20Snapshot.sol";

contract OpenZeppelinERC20SnapshotForgeTest {
    function testSnapshotsTrackBalancesAndTotalSupply() public {
        OpenZeppelinERC20SnapshotHarness token =
            new OpenZeppelinERC20SnapshotHarness();

        address alice = address(this);
        address bob = address(0xB0B);

        token.mint(alice, 100);
        uint256 first = token.snapshot();
        require(first == 1, "first id");

        require(token.transfer(bob, 40), "transfer");
        require(token.balanceOf(alice) == 60, "alice current");
        require(token.balanceOf(bob) == 40, "bob current");
        require(token.totalSupply() == 100, "supply current");

        require(token.balanceOfAt(alice, first) == 100, "alice at first");
        require(token.balanceOfAt(bob, first) == 0, "bob at first");
        require(token.totalSupplyAt(first) == 100, "supply at first");

        uint256 second = token.snapshot();
        require(second == 2, "second id");

        token.burn(bob, 10);
        require(token.balanceOf(alice) == 60, "alice after burn");
        require(token.balanceOf(bob) == 30, "bob after burn");
        require(token.totalSupply() == 90, "supply after burn");
        require(token.balanceOfAt(alice, second) == 60, "alice at second");
        require(token.balanceOfAt(bob, second) == 40, "bob at second");
        require(token.totalSupplyAt(second) == 100, "supply at second");
    }

    function testSnapshotIdValidationAndCurrentFallback() public {
        OpenZeppelinERC20SnapshotHarness token =
            new OpenZeppelinERC20SnapshotHarness();

        address alice = address(this);
        address bob = address(0xB0B);

        token.mint(alice, 50);
        uint256 first = token.snapshot();
        token.mint(alice, 25);

        require(token.balanceOfAt(alice, first) == 50, "alice historical");
        require(token.balanceOfAt(bob, first) == 0, "bob fallback");

        try token.balanceOfAt(alice, 0) returns (uint256) {
            revert("expected zero id revert");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("ERC20Snapshot: id is 0")),
                "zero id reason"
            );
        }

        try token.totalSupplyAt(first + 1) returns (uint256) {
            revert("expected future id revert");
        } catch Error(string memory reason) {
            require(
                keccak256(bytes(reason)) ==
                    keccak256(bytes("ERC20Snapshot: nonexistent id")),
                "future id reason"
            );
        }
    }

    function testRepeatedTransfersRecordOncePerSnapshotId() public {
        OpenZeppelinERC20SnapshotHarness token =
            new OpenZeppelinERC20SnapshotHarness();
        OpenZeppelinERC20SnapshotSpender bobActor =
            new OpenZeppelinERC20SnapshotSpender();

        address alice = address(this);
        address bob = address(bobActor);

        token.mint(alice, 10);
        uint256 first = token.snapshot();

        require(token.transfer(bob, 3), "transfer one");
        require(bobActor.transferToken(token, alice, 1), "transfer back");

        uint256 second = token.snapshot();

        require(token.balanceOf(alice) == 8, "alice current");
        require(token.balanceOf(bob) == 2, "bob current");
        require(token.balanceOfAt(alice, first) == 10, "alice first");
        require(token.balanceOfAt(bob, first) == 0, "bob first");
        require(token.balanceOfAt(alice, second) == 8, "alice second");
        require(token.balanceOfAt(bob, second) == 2, "bob second");
    }

    function testAllowanceTransferFromUpdatesSnapshots() public {
        OpenZeppelinERC20SnapshotHarness token =
            new OpenZeppelinERC20SnapshotHarness();
        OpenZeppelinERC20SnapshotSpender spender =
            new OpenZeppelinERC20SnapshotSpender();

        address alice = address(this);
        address bob = address(0xB0B);

        token.mint(alice, 70);
        uint256 first = token.snapshot();
        require(token.approve(address(spender), 25), "approve");
        require(
            spender.transferFromToken(token, alice, bob, 20),
            "transferFrom"
        );

        require(token.allowance(alice, address(spender)) == 5, "allowance");
        require(token.balanceOf(alice) == 50, "alice current");
        require(token.balanceOf(bob) == 20, "bob current");
        require(token.balanceOfAt(alice, first) == 70, "alice first");
        require(token.balanceOfAt(bob, first) == 0, "bob first");
    }
}

contract OpenZeppelinERC20SnapshotSpender {
    function transferToken(
        OpenZeppelinERC20SnapshotHarness token,
        address to,
        uint256 amount
    ) external returns (bool) {
        return token.transfer(to, amount);
    }

    function transferFromToken(
        OpenZeppelinERC20SnapshotHarness token,
        address from,
        address to,
        uint256 amount
    ) external returns (bool) {
        return token.transferFrom(from, to, amount);
    }
}
