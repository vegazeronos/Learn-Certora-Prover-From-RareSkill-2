// SPDX-License-Identifier: MIT
// OpenZeppelin Contracts (last updated v5.6.0) (utils/Bytes.sol)

pragma solidity ^0.8.24;

import {Math} from "./math/Math.sol";

/**
 * @dev Bytes operations.
 */
library Bytes {
    /**
     * @dev Forward search for `s` in `buffer`
     * * If `s` is present in the buffer, returns the index of the first instance
     * * If `s` is not present in the buffer, returns type(uint256).max
     *
     * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/indexOf[Javascript's `Array.indexOf`]
     */
    function indexOf(bytes memory buffer, bytes1 s) internal pure returns (uint256) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00200000, 1037618708512) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00200001, 2) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00200005, 9) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00206001, s) }
        return indexOf(buffer, s, 0);
    }

    /**
     * @dev Forward search for `s` in `buffer` starting at position `pos`
     * * If `s` is present in the buffer (at or after `pos`), returns the index of the next instance
     * * If `s` is not present in the buffer (at or after `pos`), returns type(uint256).max
     *
     * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/indexOf[Javascript's `Array.indexOf`]
     */
    function indexOf(bytes memory buffer, bytes1 s, uint256 pos) internal pure returns (uint256) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00210000, 1037618708513) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00210001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00210005, 73) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00216002, pos) }
        uint256 length = buffer.length;assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000008,length)}
        for (uint256 i = pos; i < length; ++i) {
            if (bytes1(_unsafeReadBytesOffset(buffer, i)) == s) {
                return i;
            }
        }
        return type(uint256).max;
    }

    /**
     * @dev Backward search for `s` in `buffer`
     * * If `s` is present in the buffer, returns the index of the last instance
     * * If `s` is not present in the buffer, returns type(uint256).max
     *
     * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/lastIndexOf[Javascript's `Array.lastIndexOf`]
     */
    function lastIndexOf(bytes memory buffer, bytes1 s) internal pure returns (uint256) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00230000, 1037618708515) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00230001, 2) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00230005, 9) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00236001, s) }
        return lastIndexOf(buffer, s, type(uint256).max);
    }

    /**
     * @dev Backward search for `s` in `buffer` starting at position `pos`
     * * If `s` is present in the buffer (at or before `pos`), returns the index of the previous instance
     * * If `s` is not present in the buffer (at or before `pos`), returns type(uint256).max
     *
     * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/lastIndexOf[Javascript's `Array.lastIndexOf`]
     */
    function lastIndexOf(bytes memory buffer, bytes1 s, uint256 pos) internal pure returns (uint256) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00240000, 1037618708516) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00240001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00240005, 73) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00246002, pos) }
        unchecked {
            uint256 length = buffer.length;
            for (uint256 i = Math.min(Math.saturatingAdd(pos, 1), length); i > 0; --i) {
                if (bytes1(_unsafeReadBytesOffset(buffer, i - 1)) == s) {
                    return i - 1;
                }
            }
            return type(uint256).max;
        }
    }

    /**
     * @dev Copies the content of `buffer`, from `start` (included) to the end of `buffer` into a new bytes object in
     * memory.
     *
     * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/slice[Javascript's `Array.slice`]
     */
    function slice(bytes memory buffer, uint256 start) internal pure returns (bytes memory) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00220000, 1037618708514) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00220001, 2) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00220005, 9) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00226001, start) }
        return slice(buffer, start, buffer.length);
    }

    /**
     * @dev Copies the content of `buffer`, from `start` (included) to `end` (excluded) into a new bytes object in
     * memory. The `end` argument is truncated to the length of the `buffer`.
     *
     * NOTE: replicates the behavior of https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Array/slice[Javascript's `Array.slice`]
     */
    function slice(bytes memory buffer, uint256 start, uint256 end) internal pure returns (bytes memory) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00250000, 1037618708517) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00250001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00250005, 73) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00256002, end) }
        // sanitize
        end = Math.min(end, buffer.length);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0000000d,end)}
        start = Math.min(start, end);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0000000e,start)}

        // allocate and copy
        bytes memory result = new bytes(end - start);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00010009,0)}
        assembly ("memory-safe") {
            mcopy(add(result, 0x20), add(add(buffer, 0x20), start), sub(end, start))
        }

        return result;
    }

    /**
     * @dev Moves the content of `buffer`, from `start` (included) to the end of `buffer` to the start of that buffer,
     * and shrinks the buffer length accordingly, effectively overriding the content of buffer with buffer[start:].
     *
     * NOTE: This function modifies the provided buffer in place. If you need to preserve the original buffer, use {slice} instead
     */
    function splice(bytes memory buffer, uint256 start) internal pure returns (bytes memory) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00260000, 1037618708518) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00260001, 2) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00260005, 9) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00266001, start) }
        return splice(buffer, start, buffer.length);
    }

    /**
     * @dev Moves the content of `buffer`, from `start` (included) to `end` (excluded) to the start of that buffer,
     * and shrinks the buffer length accordingly, effectively overriding the content of buffer with buffer[start:end].
     * The `end` argument is truncated to the length of the `buffer`.
     *
     * NOTE: This function modifies the provided buffer in place. If you need to preserve the original buffer, use {slice} instead
     */
    function splice(bytes memory buffer, uint256 start, uint256 end) internal pure returns (bytes memory) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00270000, 1037618708519) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00270001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00270005, 73) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00276002, end) }
        // sanitize
        end = Math.min(end, buffer.length);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0000000f,end)}
        start = Math.min(start, end);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000010,start)}

        // move and resize
        assembly ("memory-safe") {
            mcopy(add(buffer, 0x20), add(add(buffer, 0x20), start), sub(end, start))
            mstore(buffer, sub(end, start))
        }

        return buffer;
    }

    /**
     * @dev Replaces bytes in `buffer` starting at `pos` with all bytes from `replacement`.
     *
     * Parameters are clamped to valid ranges (i.e. `pos` is clamped to `[0, buffer.length]`).
     * If `pos >= buffer.length`, no replacement occurs and the buffer is returned unchanged.
     *
     * NOTE: This function modifies the provided buffer in place.
     */
    function replace(bytes memory buffer, uint256 pos, bytes memory replacement) internal pure returns (bytes memory) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00280000, 1037618708520) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00280001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00280005, 73) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00286002, replacement) }
        return replace(buffer, pos, replacement, 0, replacement.length);
    }

    /**
     * @dev Replaces bytes in `buffer` starting at `pos` with bytes from `replacement` starting at `offset`.
     * Copies at most `length` bytes from `replacement` to `buffer`.
     *
     * Parameters are clamped to valid ranges (i.e. `pos` is clamped to `[0, buffer.length]`, `offset` is
     * clamped to `[0, replacement.length]`, and `length` is clamped to `min(length, replacement.length - offset,
     * buffer.length - pos))`. If `pos >= buffer.length` or `offset >= replacement.length`, no replacement occurs
     * and the buffer is returned unchanged.
     *
     * NOTE: This function modifies the provided buffer in place.
     */
    function replace(
        bytes memory buffer,
        uint256 pos,
        bytes memory replacement,
        uint256 offset,
        uint256 length
    ) internal pure returns (bytes memory) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00290000, 1037618708521) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00290001, 5) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00290005, 4681) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00296004, length) }
        // sanitize
        pos = Math.min(pos, buffer.length);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000011,pos)}
        offset = Math.min(offset, replacement.length);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000012,offset)}
        length = Math.min(length, Math.min(replacement.length - offset, buffer.length - pos));assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000013,length)}

        // replace
        assembly ("memory-safe") {
            mcopy(add(add(buffer, 0x20), pos), add(add(replacement, 0x20), offset), length)
        }

        return buffer;
    }

    /**
     * @dev Concatenate an array of bytes into a single bytes object.
     *
     * For fixed bytes types, we recommend using the solidity built-in `bytes.concat` or (equivalent)
     * `abi.encodePacked`.
     *
     * NOTE: this could be done in assembly with a single loop that expands starting at the FMP, but that would be
     * significantly less readable. It might be worth benchmarking the savings of the full-assembly approach.
     */
    function concat(bytes[] memory buffers) internal pure returns (bytes memory) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002a0000, 1037618708522) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002a0001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002a0005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002a6000, buffers) }
        uint256 length = 0;assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0000000a,length)}
        for (uint256 i = 0; i < buffers.length; ++i) {
            length += buffers[i].length;assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000020,length)}
        }

        bytes memory result = new bytes(length);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0001000b,0)}

        uint256 offset = 0x20;assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0000000c,offset)}
        for (uint256 i = 0; i < buffers.length; ++i) {
            bytes memory input = buffers[i];assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0001001e,0)}
            assembly ("memory-safe") {
                mcopy(add(result, offset), add(input, 0x20), mload(input))
            }
            unchecked {
                offset += input.length;
            }
        }

        return result;
    }

    /**
     * @dev Split each byte in `input` into two nibbles (4 bits each)
     *
     * Example: hex"01234567" → hex"0001020304050607"
     */
    function toNibbles(bytes memory input) internal pure returns (bytes memory output) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002b0000, 1037618708523) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002b0001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002b0005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002b6000, input) }
        assembly ("memory-safe") {
            let length := mload(input)
            output := mload(0x40)
            mstore(0x40, add(add(output, 0x20), mul(length, 2)))
            mstore(output, mul(length, 2))
            for {
                let i := 0
            } lt(i, length) {
                i := add(i, 0x10)
            } {
                let chunk := shr(128, mload(add(add(input, 0x20), i)))
                chunk := and(
                    0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff,
                    or(shl(64, chunk), chunk)
                )
                chunk := and(
                    0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,
                    or(shl(32, chunk), chunk)
                )
                chunk := and(
                    0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,
                    or(shl(16, chunk), chunk)
                )
                chunk := and(
                    0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,
                    or(shl(8, chunk), chunk)
                )
                chunk := and(
                    0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,
                    or(shl(4, chunk), chunk)
                )
                mstore(add(add(output, 0x20), mul(i, 2)), chunk)
            }
        }
    }

    /**
     * @dev Returns true if the two byte buffers are equal.
     */
    function equal(bytes memory a, bytes memory b) internal pure returns (bool) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002c0000, 1037618708524) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002c0001, 2) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002c0005, 9) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002c6001, b) }
        return a.length == b.length && keccak256(a) == keccak256(b);
    }

    /**
     * @dev Reverses the byte order of a bytes32 value, converting between little-endian and big-endian.
     * Inspired by https://graphics.stanford.edu/~seander/bithacks.html#ReverseParallel[Reverse Parallel]
     */
    function reverseBytes32(bytes32 value) internal pure returns (bytes32) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002d0000, 1037618708525) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002d0001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002d0005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002d6000, value) }
        value = // swap bytes
            ((value >> 8) & 0x00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF) |
            ((value & 0x00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF) << 8);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000014,value)}
        value = // swap 2-byte long pairs
            ((value >> 16) & 0x0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF) |
            ((value & 0x0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF) << 16);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000015,value)}
        value = // swap 4-byte long pairs
            ((value >> 32) & 0x00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF) |
            ((value & 0x00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF) << 32);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000016,value)}
        value = // swap 8-byte long pairs
            ((value >> 64) & 0x0000000000000000FFFFFFFFFFFFFFFF0000000000000000FFFFFFFFFFFFFFFF) |
            ((value & 0x0000000000000000FFFFFFFFFFFFFFFF0000000000000000FFFFFFFFFFFFFFFF) << 64);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000017,value)}
        return (value >> 128) | (value << 128); // swap 16-byte long pairs
    }

    /// @dev Same as {reverseBytes32} but optimized for 128-bit values.
    function reverseBytes16(bytes16 value) internal pure returns (bytes16) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002e0000, 1037618708526) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002e0001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002e0005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002e6000, value) }
        value = // swap bytes
            ((value & 0xFF00FF00FF00FF00FF00FF00FF00FF00) >> 8) | ((value & 0x00FF00FF00FF00FF00FF00FF00FF00FF) << 8);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000018,value)}
        value = // swap 2-byte long pairs
            ((value & 0xFFFF0000FFFF0000FFFF0000FFFF0000) >> 16) | ((value & 0x0000FFFF0000FFFF0000FFFF0000FFFF) << 16);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000019,value)}
        value = // swap 4-byte long pairs
            ((value & 0xFFFFFFFF00000000FFFFFFFF00000000) >> 32) | ((value & 0x00000000FFFFFFFF00000000FFFFFFFF) << 32);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0000001a,value)}
        return (value >> 64) | (value << 64); // swap 8-byte long pairs
    }

    /// @dev Same as {reverseBytes32} but optimized for 64-bit values.
    function reverseBytes8(bytes8 value) internal pure returns (bytes8) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002f0000, 1037618708527) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002f0001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002f0005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff002f6000, value) }
        value = ((value & 0xFF00FF00FF00FF00) >> 8) | ((value & 0x00FF00FF00FF00FF) << 8);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0000001b,value)} // swap bytes
        value = ((value & 0xFFFF0000FFFF0000) >> 16) | ((value & 0x0000FFFF0000FFFF) << 16);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0000001c,value)} // swap 2-byte long pairs
        return (value >> 32) | (value << 32); // swap 4-byte long pairs
    }

    /// @dev Same as {reverseBytes32} but optimized for 32-bit values.
    function reverseBytes4(bytes4 value) internal pure returns (bytes4) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00320000, 1037618708530) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00320001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00320005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00326000, value) }
        value = ((value & 0xFF00FF00) >> 8) | ((value & 0x00FF00FF) << 8);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0000001d,value)} // swap bytes
        return (value >> 16) | (value << 16); // swap 2-byte long pairs
    }

    /// @dev Same as {reverseBytes32} but optimized for 16-bit values.
    function reverseBytes2(bytes2 value) internal pure returns (bytes2) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00310000, 1037618708529) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00310001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00310005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00316000, value) }
        return (value >> 8) | (value << 8);
    }

    /**
     * @dev Counts the number of leading zero bits a bytes array. Returns `8 * buffer.length`
     * if the buffer is all zeros.
     */
    function clz(bytes memory buffer) internal pure returns (uint256) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00300000, 1037618708528) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00300001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00300005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00306000, buffer) }
        for (uint256 i = 0; i < buffer.length; i += 0x20) {
            bytes32 chunk = _unsafeReadBytesOffset(buffer, i);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0000001f,chunk)}
            if (chunk != bytes32(0)) {
                return Math.min(8 * i + Math.clz(uint256(chunk)), 8 * buffer.length);
            }
        }
        return 8 * buffer.length;
    }

    /**
     * @dev Reads a bytes32 from a bytes array without bounds checking.
     *
     * NOTE: making this function internal would mean it could be used with memory unsafe offset, and marking the
     * assembly block as such would prevent some optimizations.
     */
    function _unsafeReadBytesOffset(bytes memory buffer, uint256 offset) private pure returns (bytes32 value) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00330000, 1037618708531) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00330001, 2) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00330005, 9) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00336001, offset) }
        // This is not memory safe in the general case, but all calls to this private function are within bounds.
        assembly ("memory-safe") {
            value := mload(add(add(buffer, 0x20), offset))
        }
    }
}
