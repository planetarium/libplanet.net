using System.Collections.Generic;
using System.Threading.Tasks;
using GraphQL;
using GraphQL.Types;

namespace Libplanet.Explorer.Tests
{
    public static class GraphQLTestUtils
    {
        public static Task<ExecutionResult> ExecuteQueryAsync<TObjectGraphType>(
            string query,
            IDictionary<string, object> userContext = null,
            object source = null)
            where TObjectGraphType : IObjectGraphType, new()
        {
            var documentExecutor = new DocumentExecuter();
            return documentExecutor.ExecuteAsync(new ExecutionOptions
            {
                Query = query,
                Schema = new Schema
                {
                    Query = new TObjectGraphType(),
                },
                UserContext = userContext,
                Root = source,
            });
        }
    }
}
