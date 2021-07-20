using Bencodex.Types;

namespace Libplanet.Action
{
    /// <summary>
    /// An action implementation which does nothing for filling type parameter taking of
    /// <see cref="IAction"/>.
    /// </summary>
    public class NullAction : IAction
    {
        public NullAction()
        {
            PlainValue = default(Null);
        }

        public IValue PlainValue
        {
            get;
            private set;
        }

        public void LoadPlainValue(
            IValue plainValue)
        {
            PlainValue = plainValue;
        }

        public IAccountStateDelta Execute(IActionContext context)
        {
            return context.PreviousStates;
        }
    }
}
