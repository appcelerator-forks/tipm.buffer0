/**
 * Buffer.js
 * @ Version 0.0.1
 */

var window = {};

var push = Array.prototype.push;
var slice = Array.prototype.slice;
var splice = Array.prototype.splice;
var toString = Object.prototype.toString;
var i2a = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'.split('');
var a2i = [];
var i = 0;

// init a2i
for (i; i < i2a.length; i++) {
  a2i[i2a[i].charCodeAt(0)] = i;
}

function getA2i (c) {
  var result = a2i[c];

  if (typeof result != 'number') {
    throw 'illegal character ' + c;
  }

  return result;
}

function verifyInt (value, max, min) {
  if (typeof (value) != 'number') {
    throw 'cannot write a non-number as a number';
  }

  if (min === undefined) {
    if (value < 0) {
      throw 'specified a negative value for writing an unsigned value';
    }

    if (value > max) {
      throw 'value is larger than maximum value for type';
    }
  } else {
    if (value < min) {
      throw 'value smaller than minimum allowed value';
    }

    if (value > max) {
      throw 'value larger than maximum allowed value';
    }
  }

  if (Math.floor(value) !== value) {
    throw 'value has a fractional component';
  }
}

function verifyIEEE754 (value, max, min) {
  if (typeof (value) != 'number') {
    throw 'cannot write a non-number as a number';
  }

  if (value > max) {
    throw 'value larger than maximum allowed value';
  }

  if (value < min) {
    throw 'value smaller than minimum allowed value';
  }
}

function readIEEE754 (buffer, offset, isBE, mLen, nBytes) {
  var
    m,
    eLen = nBytes * 8 - mLen - 1,
    eMax = (1 << eLen) - 1,
    eBias = eMax >> 1,
    nBits = -7,
    i = isBE ? 0 : (nBytes - 1),
    d = isBE ? 1 : -1,
    s = buffer[offset + i],
    e = s & ((1 << (-nBits)) - 1);

  i += d;
  s >>= (-nBits);
  nBits += eLen;

  while (nBits > 0) {
    e = e * 256 + buffer[offset + i];
    i += d;
    nBits -= 8;
  }

  m = e & ((1 << (-nBits)) - 1);
  e >>= (-nBits);
  nBits += mLen;

  while (nBits > 0) {
    m = m * 256 + buffer[offset + i];
    i += d;
    nBits -= 8;
  }

  if (e === 0) {
    e = 1 - eBias;
  } else if (e === eMax) {
    return m ? NaN : ((s ? -1 : 1) * Infinity);
  } else {
    m = m + Math.pow(2, mLen);
    e = e - eBias;
  }

  return (s ? -1 : 1) * m * Math.pow(2, e - mLen);
}

function writeIEEE754 (buffer, value, offset, isBE, mLen, nBytes) {
  var
    e,
    m,
    c,
    eLen = nBytes * 8 - mLen - 1,
    eMax = (1 << eLen) - 1,
    eBias = eMax >> 1,
    rt = mLen === 23 ? Math.pow(2, -24) - Math.pow(2, -77) : 0,
    i = isBE ? (nBytes - 1) : 0,
    d = isBE ? -1 : 1,
    s = value < 0 || (value === 0 && 1 / value < 0) ? 1 : 0;

  value = Math.abs(value);

  if (isNaN(value) || value === Infinity) {
    m = isNaN(value) ? 1 : 0;
    e = eMax;
  } else {
    e = Math.floor(Math.log(value) / Math.LN2);

    if (value * (c = Math.pow(2, -e)) < 1) {
      e--;
      c *= 2;
    }

    if (e + eBias >= 1) {
      value += rt / c;
    } else {
      value += rt * Math.pow(2, 1 - eBias);
    }

    if (value * c >= 2) {
      e++;
      c /= 2;
    }

    if (e + eBias >= eMax) {
      m = 0;
      e = eMax;
    } else if (e + eBias >= 1) {
      m = (value * c - 1) * Math.pow(2, mLen);
      e = e + eBias;
    } else {
      m = value * Math.pow(2, eBias - 1) * Math.pow(2, mLen);
      e = 0;
    }
  }

  while (mLen >= 8) {
    buffer[offset + i] = m & 255;
    i += d;
    m /= 256;
    mLen -= 8;
  }

  e = (e << mLen) | m;
  eLen += mLen;

  while (eLen > 0) {
    buffer[offset + i] = e & 255;
    i += d;
    e /= 256;
    eLen -= 8;
  }

  buffer[offset + i - d] |= s * 128;
}

/**
   * @ Name Buffer
   * @ Constructor
   * @ Description Designer to create a buffer. Currently supported encoding base64, hex and utf8.
   * @ Param {number | string | Array | ArrayBuffer | DataView | Buffer} data The data in buffer, or the number that corresponds to the size of output buffer.
   * @ Param {string} [encoding = "utf8"] encoding data if <i> data </ ​​i> the passed string.
   * @ Property {number} length buffer size in bytes.
 */
var Buffer = module.exports = function(data, encoding) {
  var
    index = 0,
    length;

  if (!(this instanceof Buffer)) {
    return new Buffer(data, encoding);
  }

  switch (typeof data) {
    case 'number':
      this.length = data;
      break;
    case 'string':
      length = data.length;
      encoding = (encoding) ? String(encoding).toLowerCase() : 'utf8';

      switch (encoding) {
        case 'base64':
          var
            groupCount = Math.floor(length / 4),
            c0,
            c1,
            c2,
            c3,
            missing = 0,
            indexIn = 0,
            len;

          if (4 * groupCount != length) {
            throw 'string length must be a multiple of four';
          }

          if (length !== 0) {
            if (data.charAt(length - 1) == '=') {
              missing++;
              groupCount--;
            }

            if (data.charAt(length - 2) == '=') {
              missing++;
            }
          }

          len = (3 * groupCount - missing);
          if (len < 0) {
            len = 0;
          }

          while (index++ < groupCount) {
            c0 = getA2i(data.charCodeAt(indexIn++));
            c1 = getA2i(data.charCodeAt(indexIn++));
            c2 = getA2i(data.charCodeAt(indexIn++));
            c3 = getA2i(data.charCodeAt(indexIn++));

            push.call(this, 255 & ((c0 << 2) | (c1 >> 4)), 255 & ((c1 << 4) | (c2 >> 2)), 255 & ((c2 << 6) | c3));
          }

          switch (missing) {
            case 0:
              break;
            case 1:
              c0 = getA2i(data.charCodeAt(indexIn++));
              c1 = getA2i(data.charCodeAt(indexIn++));
              c2 = getA2i(data.charCodeAt(indexIn++));

              push.call(this, 255 & ((c0 << 2) | (c1 >> 4)), 255 & ((c1 << 4) | (c2 >> 2)));
              break;
            case 2:
              c0 = getA2i(data.charCodeAt(indexIn++));
              c1 = getA2i(data.charCodeAt(indexIn++));

              push.call(this, 255 & ((c0 << 2) | (c1 >> 4)));
              break;
            default:
              throw 'never happen';
          }
          break;
        case 'hex':
          while (index < length) {
            push.call(this, parseInt(data.substr(index, 2), 16));
            index += 2;
          }
          break;
        case 'utf8':
          var code;

          while (index < length) {
            code = data.charCodeAt(index);

            if (code <= 127) {
              push.call(this, code);
            } else if (code <= 2047) {
              push.call(this, code >>> 6 | 192, code & 63 | 128);
            } else if (code <= 65535) {
              push.call(this, code >>> 12 | 224, code >>> 6 & 63 | 128, code & 63 | 128);
            } else if (code <= 2097151) {
              push.call(this, code >>> 18 | 240, code >>> 12 & 63 | 128, code >>> 6 & 63 | 128, code & 63 | 128);
            } else if (code <= 67108863) {
              push.call(this, code >>> 24 | 248, code >>> 18 & 63 | 128, code >>> 12 & 63 | 128, code >>> 6 & 63 | 128, code & 63 | 128);
            } else if (code <= 2147483647) {
              push.call(this, code >>> 30 | 252, code >>> 24 & 63 | 128, code >>> 18 & 63 | 128, code >>> 12 & 63 | 128, code >>> 6 & 63 | 128, code & 63 | 128);
            }

            index++;
          }
          break;
        default:
          throw 'unknown encoding';
      }
      break;
    default:
      if (data instanceof Buffer || Object.prototype.toString.call(data) === '[object Array]') {
        push.apply(this, data);
      } else if (Buffer.supportNativeBuffer) {
        if (data instanceof window.ArrayBuffer) {
          data = new window.DataView(data);
        } else if (!(data instanceof window.DataView)) {
          throw 'first argument needs to be a number, array, buffer, arrayBuffer, dataView or string';
        }

        length = data.byteLength;

        while (index < length) {
          this[index] = data.getUint8(index);
          index++;
        }

        this.length = length;
      } else {
        throw 'first argument needs to be a number, array, buffer or string';
      }
  }
};

/**
 * @type {boolean}
 */
Buffer.supportNativeBuffer = window.DataView && window.ArrayBuffer;

  /**
   * Checks if the passed object instance constructor {@ link Buffer}.
   * @ Static
   * @ Param {Object} object The object to validate.
   * @ Return {boolean} The test result.
   */
Buffer.isBuffer = function (object) {
  return (object instanceof Buffer);
};

  /**
   * Calculates the number of bytes of data transferred. Parameters are similar to {@ link Buffer}.
   * @ Static
   * @ Param {number | string | Array | ArrayBuffer | DataView | Buffer} data The data size to be calculated.
   * @ Param {string} [encoding = "utf8"] Encoding data transmitted.
   * @ Return {number} size in bytes.
   */
Buffer.byteLength = function (data, encoding) {
  return new Buffer(data, encoding).length;
};

/**
 * @param list
 * @param length
 * @return {buffer}
 */
Buffer.concat = function (list, length) {
  var
    index,
    buffer,
    pos = 0;

  if (toString.call(list) !== '[object Array]') {
    throw 'Usage: Buffer.concat(list, [length])';
  }

  if (list.length === 0) {
    return new Buffer(0);
  } else if (list.length === 1) {
    return list[0];
  }

  if (typeof length !== 'number') {
    length = 0;

    for (index = 0; index < list.length; index++) {
      length += list[index].length;
    }
  }

  buffer = new Buffer(length);

  for (index = 0; index < list.length; index++) {
    var buf = list[index];

    buf.copy(buffer, pos);
    pos += buf.length;
  }

  return buffer;
};

Buffer.prototype = {
  constructor: Buffer,

    /**
     * Copy data to the clipboard <i> targetBuffer </ i>.
     * @ Param {Buffer} targetBuffer buffer into which to copy data.
     * @ Param {number} [targetStart = 0] The position at which to insert the copied data.
     * @ Param {number} [sourceStart = 0] Start position data to be copied in the buffer.
     * @ Param {number} [sourceEnd = this.length] Target position data to be copied in the buffer.
     * @ Return {number} The new buffer length <i> targetBuffer </ i>.
     * @ Function
     */
  copy: function (targetBuffer, targetStart, sourceStart, sourceEnd) {
    var
      sourceLength = this.length,
      targetLength = targetBuffer.length,
      data;

    sourceStart = sourceStart || 0;
    sourceEnd = sourceEnd || sourceLength;
    targetStart = targetStart || 0;

    if (sourceEnd < sourceStart) {
      throw 'sourceEnd < sourceStart';
    }

    if (sourceEnd === sourceStart || targetBuffer.length === 0 || sourceLength === 0) {
      return 0;
    }

    if (targetStart < 0 || targetStart >= targetLength) {
      throw 'targetStart out of bounds';
    }

    if (sourceStart < 0 || sourceStart >= sourceLength) {
      throw 'sourceStart out of bounds';
    }

    if (sourceEnd < 0 || sourceEnd > sourceLength) {
      throw 'sourceEnd out of bounds';
    }

    if (targetLength - targetStart < sourceEnd - sourceStart) {
      sourceEnd = targetLength - targetStart + sourceStart;
    }

    data = slice.call(this, sourceStart, sourceEnd);
    data.unshift(targetStart, sourceEnd - sourceStart);
    splice.apply(targetBuffer, data);

    return targetBuffer.length;
  },

    /**
     * Converts to a string buffer.
     * @ Param {string} [encoding = utf8] encoding used to convert the buffer.
     * @ Param {number} [start = 0] Start position encoded data.
     * @ Param {number} [end = this.length] Target position encoded data.
     * @ Return {string} encodes.
     * @ Function
     */
  toString: function (encoding, start, end) {
    var result = '';
    var index = 0;
    var number = 0;
    var length = this.length;

    if (start === undefined || start < 0) {
      start = 0;
    } else if (start > length) {
      start = length;
    }

    if (end === undefined || end > length) {
      end = length;
    } else if (end < 0) {
      end = 0;
    }

    if (start == end) {
      return result;
    }

    encoding = (encoding) ? String(encoding).toLowerCase() : 'utf8';
    index = start;
    length = end - start;

    switch (encoding) {
      case 'hex':
        while (index < end) {
          number = this[index++];
          result += (number < 16 ? '0' : '') + number.toString(16);
        }
        break;
      case 'base64':
        var
          groupCount = Math.floor(length / 3),
          remaining = length - 3 * groupCount,
          b0,
          b1,
          b2,
          i = 0;

        while (i++ < groupCount) {
          b0 = this[index++] & 255;
          b1 = this[index++] & 255;
          b2 = this[index++] & 255;

          result += i2a[b0 >> 2];
          result += i2a[(b0 << 4) & 63 | (b1 >> 4)];
          result += i2a[(b1 << 2) & 63 | (b2 >> 6)];
          result += i2a[b2 & 63];
        }

        switch (remaining) {
          case 0:
            break;
          case 1:
            b0 = this[index++] & 255;

            result += i2a[b0 >> 2];
            result += i2a[(b0 << 4) & 63];
            result += '==';
            break;
          case 2:
            b0 = this[index++] & 255;
            b1 = this[index++] & 255;

            result += i2a[b0 >> 2];
            result += i2a[(b0 << 4) & 63 | (b1 >> 4)];
            result += i2a[(b1 << 2) & 63];
            result += '=';
            break;
          default:
            throw 'never happen';
        }
        break;
      case 'utf8':
        while (index < end) {
          number = this[index++];

          if (number < 128) {
            result += String.fromCharCode(number);
          } else if (number < 224) {
            result += String.fromCharCode(((31 & number) << 6) | ((63 & this[index++]) << 0));
          } else if (number < 240) {
            result += String.fromCharCode(((15 & number) << 12) | ((63 & this[index++]) << 6) | ((63 & this[index++]) << 0));
          } else if (number < 248) {
            result += String.fromCharCode(((7 & number) << 18) | ((63 & this[index++]) << 12) | ((63 & this[index++]) << 6) | ((63 & this[index++]) << 0));
          } else if (number < 252) {
            result += String.fromCharCode(((3 & number) << 24) | ((63 & this[index++]) << 18) | ((63 & this[index++]) << 12) | ((63 & this[index++]) << 6) | ((63 & this[index++]) << 0));
          } else if (number < 254) {
            result += String.fromCharCode(((1 & number) << 30) | ((63 & this[index++]) << 24) | ((63 & this[index++]) << 18) | ((63 & this[index++]) << 12) | ((63 & this[index++]) << 6) | ((63 & this[index++]) << 0));
          }
        }
        break;
      default:
        throw 'unknown encoding';
    }

    return result;
  },

    /**
     * Converts the buffer array.
     * @ Param {number} [start = 0] Start position of converted data.
     * @ Param {number} [end = this.length] The final position of converted data.
     * @ Return {Array} The result of the conversion.
     * @ Function
     */
  toArray: function (start, end) {
    var length = this.length;

    start = start || 0;
    end = end || length;

    if (end < start) {
      throw 'end < start';
    }

    if (end === start || length === 0) {
      return [];
    }

    if (start < 0 || start >= length) {
      throw 'start out of bounds';
    }

    if (end < 0 || end > length) {
      throw 'end out of bounds';
    }

    return slice.call(this, start, end);
  },

    /**
     * Converts the buffer in DataView, if this type supported by your browser.
     * @ Param {number} [start = 0] Start position data buffer.
     * @ Param {number} [end = this.length] Target position data buffer.
     * @ Return {DataView} new buffer.
     * @ Function
     */
  toDataView: function (start, end) {
    var
      dataView,
      byteLength,
      index = 0,
      length = this.length;

    if (Buffer.supportNativeBuffer) {
      throw 'DataView is not supported';
    }

    start = start || 0;
    end = end || length;

    if (end < start) {
      throw 'end < start';
    }

    if (end === start || length === 0) {
      return new window.ArrayBuffer(0);
    }

    if (start < 0 || start >= length) {
      throw 'start out of bounds';
    }

    if (end < 0 || end > length) {
      throw 'end out of bounds';
    }

    byteLength = end - start;
    dataView = new window.DataView(new window.ArrayBuffer(byteLength));

    while (start < end) {
      dataView.setUint8(index++, this[start++]);
    }

    return dataView;
  },

    /**
     * Converts the buffer ArrayBuffer, if this type supported by your browser.
     * @ Param {number} [start = 0] Start position data buffer.
     * @ Param {number} [end = this.length] Target position data buffer.
     * @ Return {ArrayBuffer} new buffer.
     * @ Function
     */
  toArrayBuffer: function (start, end) {
    if (Buffer.supportNativeBuffer) {
      throw 'ArrayBuffer is not supported';
    }

    return this.toDataView(start, end).buffer;
  },

    /**
     * Cuts buffer, leaving data from position start to position end.
     * @ Param {number} [start = 0] Start position.
     * @ Param {number} [end = this.length] final position.
     * @ Return {Buffer} new buffer.
     * @ Function
     */
  slice: function (start, end) {
    var length = this.length;

    if (start === undefined) {
      start = 0;
    }

    if (end === undefined) {
      end = length;
    }

    if (end > length) {
      throw new Error('oob');
    }

    if (start > end) {
      throw new Error('oob');
    }

    splice.call(this, 0, start);
    splice.call(this, end - start, length - end);

    return this;
  },

    /**
     * Writes the encoded data encoding from offset long length.
     * @ Param {number | string | Array | ArrayBuffer | DataView | Buffer} data
     * @ Param {number} [offset = 0]
     * @ Param {number} [length = this.length-offset]
     * @ Param {string} [encoding = "utf8"]
     * @ Return {number} The number of bytes written
     * @ Function
     */
  write: function (data, offset, length, encoding) {
    var
      remaining,
      buffer,
      byteLength;

    offset = +offset || 0;

    remaining = this.length - offset;

    if (!length) {
      length = remaining;
    } else {
      length = +length;
      if (length > remaining) {
        length = remaining;
      }
    }

    encoding = (encoding) ? String(encoding).toLowerCase() : 'utf8';

    buffer = new Buffer(data, encoding);
    byteLength = buffer.length;

    buffer = slice.call(buffer);
    buffer.unshift(offset, length);
    splice.apply(this, buffer);

    return byteLength < length ? byteLength : length;
  },

    /**
     * Fills the buffer value of value from a position start to position end.
     * @ Param {number | string} [value = 0] number or text character whose code is to be used for filling.
     * @ Param {number} [start = 0] Start position.
     * @ Param {number} [end = buffer.length] final position.
     * @ Function
     */
  fill: function (value, start, end) {
    var length = this.length;

    value = value || 0;
    start = start || 0;
    end = end || length;

    if (typeof value === 'string') {
      value = value.charCodeAt(0);
    }

    if (typeof value !== 'number' || isNaN(value)) {
      throw 'value is not a number';
    }

    if (end < start) {
      throw 'end < start';
    }

    if (end === start || length === 0) {
      return 0;
    }

    if (start < 0 || start >= length) {
      throw 'start out of bounds';
    }

    if (end < 0 || end > length) {
      throw 'end out of bounds';
    }

    while (start < end) {
      this[start++] = value;
    }
  },

  /**
   * @param offset
   * @param noAssert
   * @return {number}
   */
  readUInt8: function (offset, noAssert) {
    if (noAssert === true) {
      if (offset === undefined || offset === null) {
        throw 'missing offset';
      }

      if (offset >= this.length) {
        throw 'trying to read beyond buffer length';
      }
    }

    return this[offset];
  },

  /**
   * @param offset
   * @param noAssert
   * @return {number}
   */
  readInt8: function (offset, noAssert) {
    if (noAssert === true) {
      if (offset === undefined || offset === null) {
        throw 'missing offset';
      }

      if (offset >= this.length) {
        throw 'trying to read beyond buffer length';
      }
    }

    return !(this[offset] & 128) ? this[offset] : ((255 - this[offset] + 1) * -1);
  },

  /**
   * @param offset
   * @param isBigEndian
   * @param noAssert
   * @return {number}
   */
  readUInt16: function (offset, isBigEndian, noAssert) {
    var result;

    if (noAssert === true) {
      if (offset === undefined || offset === null) {
        throw 'missing offset';
      }

      if (typeof (isBigEndian) !== 'boolean') {
        throw 'missing or invalid endian';
      }

      if (offset + 1 >= this.length) {
        throw 'Trying to read beyond buffer length';
      }
    }

    if (isBigEndian) {
      result = this[offset] << 8;
      result |= this[offset + 1];
    } else {
      result = this[offset];
      result |= this[offset + 1] << 8;
    }

    return result;
  },

  /**
   * @param offset
   * @param noAssert
   * @return {*}
   */
  readUInt16LE: function (offset, noAssert) {
    return this.readUInt16(offset, false, noAssert);
  },

  /**
   * @param offset
   * @param noAssert
   * @return {number}
   */
  readUInt16BE: function (offset, noAssert) {
    return this.readUInt16(offset, true, noAssert);
  },

  /**
   * @param offset
   * @param isBigEndian
   * @param noAssert
   * @return {number}
   */
  readInt16: function (offset, isBigEndian, noAssert) {
    var value = this.readUInt16(offset, isBigEndian, noAssert);

    return value & 32768 ? (65535 - value + 1) * -1 : value;
  },

  /**
   * @param offset
   * @param noAssert
   * @return {number}
   */
  readInt16LE: function (offset, noAssert) {
    return this.readInt16(offset, false, noAssert);
  },

  /**
   * @param offset
   * @param noAssert
   * @return {number}
   */
  readInt16BE: function (offset, noAssert) {
    return this.readInt16(offset, true, noAssert);
  },

  /**
   * @param offset
   * @param isBigEndian
   * @param noAssert
   * @return {number}
   */
  readUInt32: function (offset, isBigEndian, noAssert) {
    var result;

    if (noAssert === true) {
      if (offset === undefined || offset === null) {
        throw 'missing offset';
      }

      if (typeof (isBigEndian) !== 'boolean') {
        throw 'missing or invalid endian';
      }

      if (offset + 3 >= this.length) {
        throw 'Trying to read beyond this length';
      }
    }

    if (isBigEndian) {
      result = this[offset + 1] << 16;
      result |= this[offset + 2] << 8;
      result |= this[offset + 3];
      result += (this[offset] << 24 >>> 0);
    } else {
      result = this[offset + 2] << 16;
      result |= this[offset + 1] << 8;
      result |= this[offset];
      result += (this[offset + 3] << 24 >>> 0);
    }

    return result;
  },

  /**
   * @param offset
   * @param noAssert
   * @return {number}
   */
  readUInt32LE: function (offset, noAssert) {
    return this.readUInt32(offset, false, noAssert);
  },

  /**
   * @param offset
   * @param noAssert
   * @return {number}
   */
  readUInt32BE: function (offset, noAssert) {
    return this.readUInt32(offset, true, noAssert);
  },

  /**
   * @param offset
   * @param isBigEndian
   * @param noAssert
   * @return {number}
   */
  readInt32: function (offset, isBigEndian, noAssert) {
    var value = this.readUInt32(offset, isBigEndian, noAssert);

    return value & 2147483648 ? (4294967295 - value + 1) * -1 : value;
  },

  /**
   * @param offset
   * @param noAssert
   * @return {number}
   */
  readInt32LE: function (offset, noAssert) {
    return this.readInt32(offset, false, noAssert);
  },

  /**
   * @param offset
   * @param noAssert
   * @return {number}
   */
  readInt32BE: function (offset, noAssert) {
    return this.readInt32(offset, true, noAssert);
  },

  /**
   * @param offset
   * @param isBigEndian
   * @param noAssert
   * @return {number}
   */
  readFloat: function (offset, isBigEndian, noAssert) {
    if (noAssert === true) {
      if (offset !== undefined && offset !== null) {
        throw 'missing offset';
      }

      if (typeof (isBigEndian) !== 'boolean') {
        throw 'missing or invalid endian';
      }

      if (offset + 3 < this.length) {
        throw 'Trying to read beyond buffer length';
      }
    }

    return readIEEE754(this, offset, isBigEndian, 23, 4);
  },

  /**
   * @param offset
   * @param noAssert
   * @return {number}
   */
  readFloatLE: function (offset, noAssert) {
    return this.readFloat(offset, false, noAssert);
  },

  /**
   * @param offset
   * @param noAssert
   * @return {number}
   */
  readFloatBE: function (offset, noAssert) {
    return this.readFloat(offset, true, noAssert);
  },

  /**
   * @param offset
   * @param isBigEndian
   * @param noAssert
   * @return {number}
   */
  readDouble: function (offset, isBigEndian, noAssert) {
    if (noAssert === true) {
      if (offset !== undefined && offset !== null) {
        throw 'missing offset';
      }

      if (typeof (isBigEndian) !== 'boolean') {
        throw 'missing or invalid endian';
      }

      if (offset + 7 < this.length) {
        throw 'Trying to read beyond buffer length';
      }
    }

    return readIEEE754(this, offset, isBigEndian, 52, 8);
  },

  /**
   * @param offset
   * @param noAssert
   * @return {number}
   */
  readDoubleLE: function (offset, noAssert) {
    return this.readDouble(offset, false, noAssert);
  },

  /**
   * @param offset
   * @param noAssert
   * @return {number}
   */
  readDoubleBE: function (offset, noAssert) {
    return this.readDouble(offset, true, noAssert);
  },

  /**
   * @param value
   * @param offset
   * @param noAssert
   */
  writeUInt8: function (value, offset, noAssert) {
    if (!noAssert) {
      if (offset === undefined || offset === null) {
        throw 'missing offset';
      }

      if (value === undefined || value === null) {
        throw 'missing value';
      }

      if (offset >= this.length) {
        throw 'trying to write beyond buffer length';
      }

      verifyInt(value, 255, undefined);
    }

    this[offset] = value;
  },

  /**
   * @param value
   * @param offset
   * @param noAssert
   */
  writeInt8: function (value, offset, noAssert) {
    if (!noAssert) {
      if (offset === undefined || offset === null) {
        throw 'missing offset';
      }

      if (value === undefined || value === null) {
        throw 'missing value';
      }

      if (offset >= this.length) {
        throw 'trying to write beyond buffer length';
      }

      verifyInt(value, 127, -128);
    }

    if (value >= 0) {
      this.writeUInt8(value, offset, noAssert);
    } else {
      this.writeUInt8(255 + value + 1, offset, noAssert);
    }
  },

  /**
   * @param value
   * @param offset
   * @param isBigEndian
   * @param noAssert
   */
  writeUInt16: function (value, offset, isBigEndian, noAssert) {
    if (!noAssert) {
      if (offset === undefined || offset === null) {
        throw 'missing offset';
      }

      if (value === undefined || value === null) {
        throw 'missing value';
      }

      if (typeof (isBigEndian) !== 'boolean') {
        throw 'missing or invalid endian';
      }

      if (offset + 1 >= this.length) {
        throw 'trying to write beyond this length';
      }

      verifyInt(value, 65535, undefined);
    }

    if (isBigEndian) {
      this[offset] = (value & 65280) >>> 8;
      this[offset + 1] = value & 255;
    } else {
      this[offset + 1] = (value & 65280) >>> 8;
      this[offset] = value & 255;
    }
  },

  /**
   * @param value
   * @param offset
   * @param noAssert
   */
  writeUInt16LE: function (value, offset, noAssert) {
    this.writeUInt16(value, offset, false, noAssert);
  },

  /**
   * @param value
   * @param offset
   * @param noAssert
   */
  writeUInt16BE: function (value, offset, noAssert) {
    this.writeUInt16(value, offset, true, noAssert);
  },

  /**
   * @param value
   * @param offset
   * @param isBigEndian
   * @param noAssert
   */
  writeInt16: function (value, offset, isBigEndian, noAssert) {
    if (!noAssert) {
      verifyInt(value, 32767, -32768);
    }

    this.writeUInt16(value < 0 ? 65535 + value + 1 : value, offset, isBigEndian, noAssert);
  },

  /**
   * @param value
   * @param offset
   * @param noAssert
   */
  writeInt16LE: function (value, offset, noAssert) {
    this.writeInt16(value, offset, false, noAssert);
  },

  /**
   * @param value
   * @param offset
   * @param noAssert
   */
  writeInt16BE: function (value, offset, noAssert) {
    this.writeUInt16(value, offset, true, noAssert);
  },

  /**
   * @param value
   * @param offset
   * @param isBigEndian
   * @param noAssert
   */
  writeUInt32: function (value, offset, isBigEndian, noAssert) {
    if (!noAssert) {
      if (offset === undefined || offset === null) {
        throw 'missing offset';
      }

      if (value === undefined || value === null) {
        throw 'missing value';
      }

      if (typeof (isBigEndian) !== 'boolean') {
        throw 'missing or invalid endian';
      }

      if (offset + 3 >= this.length) {
        throw 'trying to write beyond this length';
      }

      verifyInt(value, 4294967295, undefined);
    }

    if (isBigEndian) {
      this[offset] = (value >>> 24) & 255;
      this[offset + 1] = (value >>> 16) & 255;
      this[offset + 2] = (value >>> 8) & 255;
      this[offset + 3] = value & 255;
    } else {
      this[offset + 3] = (value >>> 24) & 255;
      this[offset + 2] = (value >>> 16) & 255;
      this[offset + 1] = (value >>> 8) & 255;
      this[offset] = value & 255;
    }
  },

  /**
   * @param value
   * @param offset
   * @param noAssert
   */
  writeUInt32LE: function (value, offset, noAssert) {
    this.writeUInt32(value, offset, false, noAssert);
  },

  /**
   * @param value
   * @param offset
   * @param noAssert
   */
  writeUInt32BE: function (value, offset, noAssert) {
    this.writeUInt32(value, offset, true, noAssert);
  },

  /**
   * @param value
   * @param offset
   * @param isBigEndian
   * @param noAssert
   */
  writeInt32: function (value, offset, isBigEndian, noAssert) {
    if (!noAssert) {
      verifyInt(value, 2147483647, -2147483648);
    }

    this.writeUInt32(value < 0 ? 4294967295 + value + 1 : value, offset, isBigEndian, noAssert);
  },

  /**
   * @param value
   * @param offset
   * @param noAssert
   */
  writeInt32LE: function (value, offset, noAssert) {
    this.writeInt32(value, offset, false, noAssert);
  },

  /**
   * @param value
   * @param offset
   * @param noAssert
   */
  writeInt32BE: function (value, offset, noAssert) {
    this.writeInt32(value, offset, true, noAssert);
  },

  /**
   * @param value
   * @param offset
   * @param isBigEndian
   * @param noAssert
   */
  writeFloat: function (value, offset, isBigEndian, noAssert) {
    if (!noAssert) {
      if (offset === undefined || offset === null) {
        throw 'missing offset';
      }

      if (value === undefined || value === null) {
        throw 'missing value';
      }

      if (typeof (isBigEndian) !== 'boolean') {
        throw 'missing or invalid endian';
      }

      if (offset + 3 >= this.length) {
        throw 'trying to write beyond this length';
      }

      verifyIEEE754(value, 3.4028234663852886e+38, -3.4028234663852886e+38);
    }

    writeIEEE754(this, value, offset, isBigEndian, 23, 4);
  },

  /**
   * @param value
   * @param offset
   * @param noAssert
   */
  writeFloatLE: function (value, offset, noAssert) {
    this.writeFloat(value, offset, false, noAssert);
  },

  /**
   * @param value
   * @param offset
   * @param noAssert
   */
  writeFloatBE: function (value, offset, noAssert) {
    this.writeFloat(value, offset, true, noAssert);
  },

  /**
   * @param value
   * @param offset
   * @param isBigEndian
   * @param noAssert
   */
  writeDouble: function (value, offset, isBigEndian, noAssert) {
    if (!noAssert) {
      if (offset === undefined || offset === null) {
        throw 'missing offset';
      }

      if (value === undefined || value === null) {
        throw 'missing value';
      }

      if (typeof (isBigEndian) !== 'boolean') {
        throw 'missing or invalid endian';
      }

      if (offset + 7 >= this.length) {
        throw 'trying to write beyond this length';
      }

      verifyIEEE754(value, 1.7976931348623157E+308, -1.7976931348623157E+308);
    }

    writeIEEE754(this, value, offset, isBigEndian, 52, 8);
  },

  /**
   * @param value
   * @param offset
   * @param noAssert
   */
  writeDoubleLE: function (value, offset, noAssert) {
    this.writeDouble(value, offset, false, noAssert);
  },

  /**
   * @param value
   * @param offset
   * @param noAssert
   */
  writeDoubleBE: function (value, offset, noAssert) {
    this.writeDouble(value, offset, true, noAssert);
  }
};