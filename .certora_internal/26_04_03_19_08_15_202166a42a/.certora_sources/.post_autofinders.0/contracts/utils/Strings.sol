// SPDX-License-Identifier: MIT
// OpenZeppelin Contracts (last updated v5.6.0) (utils/Strings.sol)

pragma solidity ^0.8.24;

import {Math} from "./math/Math.sol";
import {SafeCast} from "./math/SafeCast.sol";
import {SignedMath} from "./math/SignedMath.sol";
import {Bytes} from "./Bytes.sol";

/**
 * @dev String operations.
 */
library Strings {
    using SafeCast for *;

    bytes16 private constant HEX_DIGITS = "0123456789abcdef";
    uint8 private constant ADDRESS_LENGTH = 20;
    uint256 private constant SPECIAL_CHARS_LOOKUP =
        0xffffffff | // first 32 bits corresponding to the control characters (U+0000 to U+001F)
            (1 << 0x22) | // double quote
            (1 << 0x5c); // backslash

    /**
     * @dev The `value` string doesn't fit in the specified `length`.
     */
    error StringsInsufficientHexLength(uint256 value, uint256 length);

    /**
     * @dev The string being parsed contains characters that are not in scope of the given base.
     */
    error StringsInvalidChar();

    /**
     * @dev The string being parsed is not a properly formatted address.
     */
    error StringsInvalidAddressFormat();

    /**
     * @dev Converts a `uint256` to its ASCII `string` decimal representation.
     */
    function toString(uint256 value) internal pure returns (string memory) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00380000, 1037618708536) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00380001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00380005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00386000, value) }
        unchecked {
            uint256 length = Math.log10(value) + 1;
            string memory buffer = new string(length);
            uint256 ptr;
            assembly ("memory-safe") {
                ptr := add(add(buffer, 0x20), length)
            }
            while (true) {
                ptr--;
                assembly ("memory-safe") {
                    mstore8(ptr, byte(mod(value, 10), HEX_DIGITS))
                }
                value /= 10;assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000047,value)}
                if (value == 0) break;
            }
            return buffer;
        }
    }

    /**
     * @dev Converts a `int256` to its ASCII `string` decimal representation.
     */
    function toStringSigned(int256 value) internal pure returns (string memory) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00390000, 1037618708537) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00390001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00390005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00396000, value) }
        return string.concat(value < 0 ? "-" : "", toString(SignedMath.abs(value)));
    }

    /**
     * @dev Converts a `uint256` to its ASCII `string` hexadecimal representation.
     */
    function toHexString(uint256 value) internal pure returns (string memory) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003b0000, 1037618708539) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003b0001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003b0005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003b6000, value) }
        unchecked {
            return toHexString(value, Math.log256(value) + 1);
        }
    }

    /**
     * @dev Converts a `uint256` to its ASCII `string` hexadecimal representation with fixed length.
     */
    function toHexString(uint256 value, uint256 length) internal pure returns (string memory) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003c0000, 1037618708540) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003c0001, 2) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003c0005, 9) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003c6001, length) }
        uint256 localValue = value;assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000021,localValue)}
        bytes memory buffer = new bytes(2 * length + 2);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00010022,0)}
        buffer[0] = "0";bytes1 certora_local59 = buffer[0];assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0000003b,certora_local59)}
        buffer[1] = "x";bytes1 certora_local60 = buffer[1];assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0000003c,certora_local60)}
        for (uint256 i = 2 * length + 1; i > 1; --i) {
            buffer[i] = HEX_DIGITS[localValue & 0xf];bytes1 certora_local64 = buffer[i];assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000040,certora_local64)}
            localValue >>= 4;assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000041,localValue)}
        }
        if (localValue != 0) {
            revert StringsInsufficientHexLength(value, length);
        }
        return string(buffer);
    }

    /**
     * @dev Converts an `address` with fixed length of 20 bytes to its not checksummed ASCII `string` hexadecimal
     * representation.
     */
    function toHexString(address addr) internal pure returns (string memory) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003a0000, 1037618708538) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003a0001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003a0005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003a6000, addr) }
        return toHexString(uint256(uint160(addr)), ADDRESS_LENGTH);
    }

    /**
     * @dev Converts an `address` with fixed length of 20 bytes to its checksummed ASCII `string` hexadecimal
     * representation, according to EIP-55.
     */
    function toChecksumHexString(address addr) internal pure returns (string memory) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003d0000, 1037618708541) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003d0001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003d0005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003d6000, addr) }
        bytes memory buffer = bytes(toHexString(addr));assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00010023,0)}

        // hash the hex part of buffer (skip length + 2 bytes, length 40)
        uint256 hashValue;assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000024,hashValue)}
        assembly ("memory-safe") {
            hashValue := shr(96, keccak256(add(buffer, 0x22), 40))
        }

        for (uint256 i = 41; i > 1; --i) {
            // possible values for buffer[i] are 48 (0) to 57 (9) and 97 (a) to 102 (f)
            if (hashValue & 0xf > 7 && uint8(buffer[i]) > 96) {
                // case shift by xoring with 0x20
                buffer[i] ^= 0x20;
            }
            hashValue >>= 4;assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000042,hashValue)}
        }
        return string(buffer);
    }

    /**
     * @dev Converts a `bytes` buffer to its ASCII `string` hexadecimal representation.
     */
    function toHexString(bytes memory input) internal pure returns (string memory) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003e0000, 1037618708542) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003e0001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003e0005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003e6000, input) }
        unchecked {
            bytes memory buffer = new bytes(2 * input.length + 2);
            buffer[0] = "0";
            buffer[1] = "x";
            for (uint256 i = 0; i < input.length; ++i) {
                uint8 v = uint8(input[i]);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000043,v)}
                buffer[2 * i + 2] = HEX_DIGITS[v >> 4];bytes1 certora_local72 = buffer[2 * i + 2];assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000048,certora_local72)}
                buffer[2 * i + 3] = HEX_DIGITS[v & 0xf];bytes1 certora_local73 = buffer[2 * i + 3];assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000049,certora_local73)}
            }
            return string(buffer);
        }
    }

    /**
     * @dev Returns true if the two strings are equal.
     */
    function equal(string memory a, string memory b) internal pure returns (bool) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003f0000, 1037618708543) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003f0001, 2) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003f0005, 9) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff003f6001, b) }
        return Bytes.equal(bytes(a), bytes(b));
    }

    /**
     * @dev Parse a decimal string and returns the value as a `uint256`.
     *
     * Requirements:
     * - The string must be formatted as `[0-9]*`
     * - The result must fit into an `uint256` type
     */
    function parseUint(string memory input) internal pure returns (uint256) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00400000, 1037618708544) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00400001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00400005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00406000, input) }
        return parseUint(input, 0, bytes(input).length);
    }

    /**
     * @dev Variant of {parseUint-string} that parses a substring of `input` located between position `begin` (included) and
     * `end` (excluded).
     *
     * Requirements:
     * - The substring must be formatted as `[0-9]*`
     * - The result must fit into an `uint256` type
     */
    function parseUint(string memory input, uint256 begin, uint256 end) internal pure returns (uint256) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00410000, 1037618708545) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00410001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00410005, 73) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00416002, end) }
        (bool success, uint256 value) = tryParseUint(input, begin, end);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00010025,0)}
        if (!success) revert StringsInvalidChar();
        return value;
    }

    /**
     * @dev Variant of {parseUint-string} that returns false if the parsing fails because of an invalid character.
     *
     * NOTE: This function will revert if the result does not fit in a `uint256`.
     */
    function tryParseUint(string memory input) internal pure returns (bool success, uint256 value) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00420000, 1037618708546) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00420001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00420005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00426000, input) }
        return _tryParseUintUncheckedBounds(input, 0, bytes(input).length);
    }

    /**
     * @dev Variant of {parseUint-string-uint256-uint256} that returns false if the parsing fails because of an invalid
     * character.
     *
     * NOTE: This function will revert if the result does not fit in a `uint256`.
     */
    function tryParseUint(
        string memory input,
        uint256 begin,
        uint256 end
    ) internal pure returns (bool success, uint256 value) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00430000, 1037618708547) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00430001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00430005, 73) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00436002, end) }
        if (end > bytes(input).length || begin > end) return (false, 0);
        return _tryParseUintUncheckedBounds(input, begin, end);
    }

    /**
     * @dev Implementation of {tryParseUint-string-uint256-uint256} that does not check bounds. Caller should make sure that
     * `begin <= end <= input.length`. Other inputs would result in undefined behavior.
     */
    function _tryParseUintUncheckedBounds(
        string memory input,
        uint256 begin,
        uint256 end
    ) private pure returns (bool success, uint256 value) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00440000, 1037618708548) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00440001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00440005, 73) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00446002, end) }
        bytes memory buffer = bytes(input);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00010026,0)}

        uint256 result = 0;assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000027,result)}
        for (uint256 i = begin; i < end; ++i) {
            uint8 chr = _tryParseChr(bytes1(_unsafeReadBytesOffset(buffer, i)));assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0000003d,chr)}
            if (chr > 9) return (false, 0);
            result *= 10;assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000044,result)}
            result += chr;assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000045,result)}
        }
        return (true, result);
    }

    /**
     * @dev Parse a decimal string and returns the value as a `int256`.
     *
     * Requirements:
     * - The string must be formatted as `[-+]?[0-9]*`
     * - The result must fit in an `int256` type.
     */
    function parseInt(string memory input) internal pure returns (int256) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00450000, 1037618708549) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00450001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00450005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00456000, input) }
        return parseInt(input, 0, bytes(input).length);
    }

    /**
     * @dev Variant of {parseInt-string} that parses a substring of `input` located between position `begin` (included) and
     * `end` (excluded).
     *
     * Requirements:
     * - The substring must be formatted as `[-+]?[0-9]*`
     * - The result must fit in an `int256` type.
     */
    function parseInt(string memory input, uint256 begin, uint256 end) internal pure returns (int256) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00460000, 1037618708550) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00460001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00460005, 73) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00466002, end) }
        (bool success, int256 value) = tryParseInt(input, begin, end);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00010028,0)}
        if (!success) revert StringsInvalidChar();
        return value;
    }

    /**
     * @dev Variant of {parseInt-string} that returns false if the parsing fails because of an invalid character or if
     * the result does not fit in a `int256`.
     *
     * NOTE: This function will revert if the absolute value of the result does not fit in a `uint256`.
     */
    function tryParseInt(string memory input) internal pure returns (bool success, int256 value) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00470000, 1037618708551) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00470001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00470005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00476000, input) }
        return _tryParseIntUncheckedBounds(input, 0, bytes(input).length);
    }

    uint256 private constant ABS_MIN_INT256 = 2 ** 255;

    /**
     * @dev Variant of {parseInt-string-uint256-uint256} that returns false if the parsing fails because of an invalid
     * character or if the result does not fit in a `int256`.
     *
     * NOTE: This function will revert if the absolute value of the result does not fit in a `uint256`.
     */
    function tryParseInt(
        string memory input,
        uint256 begin,
        uint256 end
    ) internal pure returns (bool success, int256 value) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00540000, 1037618708564) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00540001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00540005, 73) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00546002, end) }
        if (end > bytes(input).length || begin > end) return (false, 0);
        return _tryParseIntUncheckedBounds(input, begin, end);
    }

    /**
     * @dev Implementation of {tryParseInt-string-uint256-uint256} that does not check bounds. Caller should make sure that
     * `begin <= end <= input.length`. Other inputs would result in undefined behavior.
     */
    function _tryParseIntUncheckedBounds(
        string memory input,
        uint256 begin,
        uint256 end
    ) private pure returns (bool success, int256 value) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00530000, 1037618708563) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00530001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00530005, 73) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00536002, end) }
        bytes memory buffer = bytes(input);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00010029,0)}

        // Check presence of a negative sign.
        bytes1 sign = begin == end ? bytes1(0) : bytes1(_unsafeReadBytesOffset(buffer, begin));assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0000002a,sign)} // don't do out-of-bound (possibly unsafe) read if sub-string is empty
        bool positiveSign = sign == bytes1("+");assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0000002b,positiveSign)}
        bool negativeSign = sign == bytes1("-");assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0000002c,negativeSign)}
        uint256 offset = (positiveSign || negativeSign).toUint();assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0000002d,offset)}

        (bool absSuccess, uint256 absValue) = tryParseUint(input, begin + offset, end);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0001002e,0)}

        if (absSuccess && absValue < ABS_MIN_INT256) {
            return (true, negativeSign ? -int256(absValue) : int256(absValue));
        } else if (absSuccess && negativeSign && absValue == ABS_MIN_INT256) {
            return (true, type(int256).min);
        } else return (false, 0);
    }

    /**
     * @dev Parse a hexadecimal string (with or without "0x" prefix), and returns the value as a `uint256`.
     *
     * Requirements:
     * - The string must be formatted as `(0x)?[0-9a-fA-F]*`
     * - The result must fit in an `uint256` type.
     */
    function parseHexUint(string memory input) internal pure returns (uint256) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00520000, 1037618708562) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00520001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00520005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00526000, input) }
        return parseHexUint(input, 0, bytes(input).length);
    }

    /**
     * @dev Variant of {parseHexUint-string} that parses a substring of `input` located between position `begin` (included) and
     * `end` (excluded).
     *
     * Requirements:
     * - The substring must be formatted as `(0x)?[0-9a-fA-F]*`
     * - The result must fit in an `uint256` type.
     */
    function parseHexUint(string memory input, uint256 begin, uint256 end) internal pure returns (uint256) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00550000, 1037618708565) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00550001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00550005, 73) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00556002, end) }
        (bool success, uint256 value) = tryParseHexUint(input, begin, end);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0001002f,0)}
        if (!success) revert StringsInvalidChar();
        return value;
    }

    /**
     * @dev Variant of {parseHexUint-string} that returns false if the parsing fails because of an invalid character.
     *
     * NOTE: This function will revert if the result does not fit in a `uint256`.
     */
    function tryParseHexUint(string memory input) internal pure returns (bool success, uint256 value) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00560000, 1037618708566) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00560001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00560005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00566000, input) }
        return _tryParseHexUintUncheckedBounds(input, 0, bytes(input).length);
    }

    /**
     * @dev Variant of {parseHexUint-string-uint256-uint256} that returns false if the parsing fails because of an
     * invalid character.
     *
     * NOTE: This function will revert if the result does not fit in a `uint256`.
     */
    function tryParseHexUint(
        string memory input,
        uint256 begin,
        uint256 end
    ) internal pure returns (bool success, uint256 value) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004a0000, 1037618708554) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004a0001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004a0005, 73) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004a6002, end) }
        if (end > bytes(input).length || begin > end) return (false, 0);
        return _tryParseHexUintUncheckedBounds(input, begin, end);
    }

    /**
     * @dev Implementation of {tryParseHexUint-string-uint256-uint256} that does not check bounds. Caller should make sure that
     * `begin <= end <= input.length`. Other inputs would result in undefined behavior.
     */
    function _tryParseHexUintUncheckedBounds(
        string memory input,
        uint256 begin,
        uint256 end
    ) private pure returns (bool success, uint256 value) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004b0000, 1037618708555) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004b0001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004b0005, 73) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004b6002, end) }
        bytes memory buffer = bytes(input);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00010030,0)}

        // skip 0x prefix if present
        bool hasPrefix = (end > begin + 1) && bytes2(_unsafeReadBytesOffset(buffer, begin)) == bytes2("0x");assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000031,hasPrefix)} // don't do out-of-bound (possibly unsafe) read if sub-string is empty
        uint256 offset = hasPrefix.toUint() * 2;assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000032,offset)}

        uint256 result = 0;assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000033,result)}
        for (uint256 i = begin + offset; i < end; ++i) {
            uint8 chr = _tryParseChr(bytes1(_unsafeReadBytesOffset(buffer, i)));assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0000003e,chr)}
            if (chr > 15) return (false, 0);
            result *= 16;assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000046,result)}
            unchecked {
                // Multiplying by 16 is equivalent to a shift of 4 bits (with additional overflow check).
                // This guarantees that adding a value < 16 will not cause an overflow, hence the unchecked.
                result += chr;
            }
        }
        return (true, result);
    }

    /**
     * @dev Parse a hexadecimal string (with or without "0x" prefix), and returns the value as an `address`.
     *
     * Requirements:
     * - The string must be formatted as `(0x)?[0-9a-fA-F]{40}`
     */
    function parseAddress(string memory input) internal pure returns (address) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004c0000, 1037618708556) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004c0001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004c0005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004c6000, input) }
        return parseAddress(input, 0, bytes(input).length);
    }

    /**
     * @dev Variant of {parseAddress-string} that parses a substring of `input` located between position `begin` (included) and
     * `end` (excluded).
     *
     * Requirements:
     * - The substring must be formatted as `(0x)?[0-9a-fA-F]{40}`
     */
    function parseAddress(string memory input, uint256 begin, uint256 end) internal pure returns (address) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00480000, 1037618708552) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00480001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00480005, 73) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00486002, end) }
        (bool success, address value) = tryParseAddress(input, begin, end);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00010034,0)}
        if (!success) revert StringsInvalidAddressFormat();
        return value;
    }

    /**
     * @dev Variant of {parseAddress-string} that returns false if the parsing fails because the input is not a properly
     * formatted address. See {parseAddress-string} requirements.
     */
    function tryParseAddress(string memory input) internal pure returns (bool success, address value) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00490000, 1037618708553) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00490001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00490005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00496000, input) }
        return tryParseAddress(input, 0, bytes(input).length);
    }

    /**
     * @dev Variant of {parseAddress-string-uint256-uint256} that returns false if the parsing fails because input is not a properly
     * formatted address. See {parseAddress-string-uint256-uint256} requirements.
     */
    function tryParseAddress(
        string memory input,
        uint256 begin,
        uint256 end
    ) internal pure returns (bool success, address value) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004f0000, 1037618708559) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004f0001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004f0005, 73) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004f6002, end) }
        if (end > bytes(input).length || begin > end) return (false, address(0));

        bool hasPrefix = (end > begin + 1) && bytes2(_unsafeReadBytesOffset(bytes(input), begin)) == bytes2("0x");assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000035,hasPrefix)} // don't do out-of-bound (possibly unsafe) read if sub-string is empty
        uint256 expectedLength = 40 + hasPrefix.toUint() * 2;assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000036,expectedLength)}

        // check that input is the correct length
        if (end - begin == expectedLength) {
            // length guarantees that this does not overflow, and value is at most type(uint160).max
            (bool s, uint256 v) = _tryParseHexUintUncheckedBounds(input, begin, end);
            return (s, address(uint160(v)));
        } else {
            return (false, address(0));
        }
    }

    function _tryParseChr(bytes1 chr) private pure returns (uint8) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00500000, 1037618708560) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00500001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00500005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00506000, chr) }
        uint8 value = uint8(chr);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000037,value)}

        // Try to parse `chr`:
        // - Case 1: [0-9]
        // - Case 2: [a-f]
        // - Case 3: [A-F]
        // - otherwise not supported
        unchecked {
            if (value > 47 && value < 58) value -= 48;
            else if (value > 96 && value < 103) value -= 87;
            else if (value > 64 && value < 71) value -= 55;
            else return type(uint8).max;
        }

        return value;
    }

    /**
     * @dev Escape special characters in JSON strings. This can be useful to prevent JSON injection in NFT metadata.
     *
     * WARNING: This function should only be used in double quoted JSON strings. Single quotes are not escaped.
     *
     * NOTE: This function escapes backslashes (including those in \uXXXX sequences) and the characters in ranges
     * defined in section 2.5 of RFC-4627 (U+0000 to U+001F, U+0022 and U+005C). All control characters in U+0000
     * to U+001F are escaped (\b, \t, \n, \f, \r use short form; others use \u00XX). ECMAScript's `JSON.parse` does
     * recover escaped unicode characters that are not in this range, but other tooling may provide different results.
     */
    function escapeJSON(string memory input) internal pure returns (string memory) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00510000, 1037618708561) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00510001, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00510005, 1) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff00516000, input) }
        bytes memory buffer = bytes(input);assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00010038,0)}

        // Put output at the FMP. Memory will be reserved later when we figure out the actual length of the escaped
        // string. All write are done using _unsafeWriteBytesOffset, which avoid the (expensive) length checks for
        // each character written.
        bytes memory output;assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00010039,0)}
        assembly ("memory-safe") {
            output := mload(0x40)
        }
        uint256 outputLength = 0;assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0000003a,outputLength)}

        for (uint256 i = 0; i < buffer.length; ++i) {
            uint8 char = uint8(bytes1(_unsafeReadBytesOffset(buffer, i)));assembly ("memory-safe"){mstore(0xffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff0000003f,char)}
            if (((SPECIAL_CHARS_LOOKUP & (1 << char)) != 0)) {
                _unsafeWriteBytesOffset(output, outputLength++, "\\");
                if (char == 0x08) _unsafeWriteBytesOffset(output, outputLength++, "b");
                else if (char == 0x09) _unsafeWriteBytesOffset(output, outputLength++, "t");
                else if (char == 0x0a) _unsafeWriteBytesOffset(output, outputLength++, "n");
                else if (char == 0x0c) _unsafeWriteBytesOffset(output, outputLength++, "f");
                else if (char == 0x0d) _unsafeWriteBytesOffset(output, outputLength++, "r");
                else if (char == 0x5c) _unsafeWriteBytesOffset(output, outputLength++, "\\");
                else if (char == 0x22) {
                    // solhint-disable-next-line quotes
                    _unsafeWriteBytesOffset(output, outputLength++, '"');
                } else {
                    // U+0000 to U+001F without short form: output \u00XX
                    _unsafeWriteBytesOffset(output, outputLength++, "u");
                    _unsafeWriteBytesOffset(output, outputLength++, "0");
                    _unsafeWriteBytesOffset(output, outputLength++, "0");
                    _unsafeWriteBytesOffset(output, outputLength++, HEX_DIGITS[char >> 4]);
                    _unsafeWriteBytesOffset(output, outputLength++, HEX_DIGITS[char & 0x0f]);
                }
            } else {
                _unsafeWriteBytesOffset(output, outputLength++, bytes1(char));
            }
        }
        // write the actual length and reserve memory
        assembly ("memory-safe") {
            mstore(output, outputLength)
            mstore(0x40, add(output, add(outputLength, 0x20)))
        }

        return string(output);
    }

    /**
     * @dev Reads a bytes32 from a bytes array without bounds checking.
     *
     * NOTE: making this function internal would mean it could be used with memory unsafe offset, and marking the
     * assembly block as such would prevent some optimizations.
     */
    function _unsafeReadBytesOffset(bytes memory buffer, uint256 offset) private pure returns (bytes32 value) {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004d0000, 1037618708557) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004d0001, 2) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004d0005, 9) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004d6001, offset) }
        // This is not memory safe in the general case, but all calls to this private function are within bounds.
        assembly ("memory-safe") {
            value := mload(add(add(buffer, 0x20), offset))
        }
    }

    /**
     * @dev Write a bytes1 to a bytes array without bounds checking.
     *
     * NOTE: making this function internal would mean it could be used with memory unsafe offset, and marking the
     * assembly block as such would prevent some optimizations.
     */
    function _unsafeWriteBytesOffset(bytes memory buffer, uint256 offset, bytes1 value) private pure {assembly ("memory-safe") { mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004e0000, 1037618708558) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004e0001, 3) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004e0005, 73) mstore(0xffffff6e4604afefe123321beef1b01fffffffffffffffffffffffff004e6002, value) }
        // This is not memory safe in the general case, but all calls to this private function are within bounds.
        assembly ("memory-safe") {
            mstore8(add(add(buffer, 0x20), offset), shr(248, value))
        }
    }
}
