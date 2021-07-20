using System;

namespace Libplanet.Explorer.Tests
{
    public static class TestUtils
    {
        private static readonly Random _random;

        static TestUtils()
        {
            _random = new Random();
        }

        public static byte[] GetRandomBytes(int size)
        {
            var bytes = new byte[size];
            _random.NextBytes(bytes);
            return bytes;
        }

        public static int GetRandomNumber() => _random.Next();
    }
}
