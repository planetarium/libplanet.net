using Bencodex.Types;
using Libplanet.Action;

namespace Libplanet.Explorer.Tests.Common.Action
{
    public class NoOpAction : IAction
    {
        public void LoadPlainValue(IValue plainValue)
        {
        }

        public IAccountStateDelta Execute(IActionContext context)
            => context.PreviousStates;

        public IValue PlainValue => default(Null);
    }
}
