using System;
using Libplanet.Explorer.GraphTypes;
using Xunit;

namespace Libplanet.Explorer.Tests.GraphTypes
{
    public class AddressTypeTest : ScalarGraphTypeTestBase<AddressType>
    {
        [Fact]
        public void Serialize()
        {
            var randomBytes = TestUtils.GetRandomBytes(Address.Size);
            var randomAddress = new Address(randomBytes);
            object serialized = _type.Serialize(randomAddress);
            Assert.Equal(randomAddress.ToString(), serialized);
        }

        [Theory]
        [InlineData(null)]
        [InlineData(0)]
        [InlineData("")]
        public void Serialize_ReturnsItselfIfNotAddressType(object value)
        {
            Assert.Equal(value, _type.Serialize(value));
        }

        [Fact]
        public void ParseValue()
        {
            Assert.Null(_type.ParseValue(null));
            Assert.Equal(new Address(), _type.ParseValue("0x0000000000000000000000000000000000000000"));
        }

        [Fact]
        public void ParseValue_ThrowsArgumentException()
        {
            Assert.Throws<ArgumentException>(() => _type.ParseValue(0));
            Assert.Throws<ArgumentException>(() => _type.ParseValue(new Address()));
            Assert.Throws<ArgumentException>(() => _type.ParseValue(new object()));
        }
    }
}
