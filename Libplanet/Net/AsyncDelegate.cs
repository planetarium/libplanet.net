#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;

namespace Libplanet.Net
{
    public class AsyncDelegate<T>
    {
        private IEnumerable<Func<T, Task>> _functions;

        public AsyncDelegate()
        {
            _functions = new List<Func<T, Task>>();
        }

        public void Register(Func<T, Task> func)
        {
#pragma warning disable PC002
            // Usage of a .NET Standard API that isn’t available on the .NET Framework 4.6.1
#if NETFRAMEWORK && !NET48 && !NET472 && !NET471
            _functions = _functions.Concat(new[] { func });
#else
            _functions = _functions.Append(func);
#endif
#pragma warning restore PC002
        }

        public void Unregister(Func<T, Task> func)
        {
            _functions = _functions.Where(f => !f.Equals(func));
        }

        public async Task InvokeAsync(T arg)
        {
            IEnumerable<Task> tasks = _functions.Select(f => f(arg));
            await Task.WhenAll(tasks);
        }
    }
}
