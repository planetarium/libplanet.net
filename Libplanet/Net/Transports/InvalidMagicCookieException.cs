using System;
using System.Collections.Generic;
using System.Collections.Immutable;

namespace Libplanet.Net.Transports
{
    public class InvalidMagicCookieException : Exception
    {
        public InvalidMagicCookieException(IEnumerable<byte> expected, IEnumerable<byte> actual)
        {
            Expected = expected.ToImmutableArray();
            Actual = actual.ToImmutableArray();
        }

        public InvalidMagicCookieException(
            IEnumerable<byte> expected,
            IEnumerable<byte> actual,
            string message)
            : base(message)
        {
            Expected = expected.ToImmutableArray();
            Actual = actual.ToImmutableArray();
        }

        public InvalidMagicCookieException(
            IEnumerable<byte> expected,
            IEnumerable<byte> actual,
            string message,
            Exception innerException)
            : base(message, innerException)
        {
            Expected = expected.ToImmutableArray();
            Actual = actual.ToImmutableArray();
        }

        public ImmutableArray<byte> Expected { get; private set; }

        public ImmutableArray<byte> Actual { get; private set; }
    }
}
