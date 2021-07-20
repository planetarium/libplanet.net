using GraphQL.Types;

namespace Libplanet.Explorer.Tests.GraphTypes
{
    public class ScalarGraphTypeTestBase<T>
        where T : ScalarGraphType, new()
    {
        protected readonly T _type = new T();
    }
}
