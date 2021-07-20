using System;
using System.Collections.Immutable;
using System.Linq;
using System.Reflection;
using Bencodex.Types;
using Libplanet.Action;
using Libplanet.Explorer.Controllers;
using Microsoft.AspNetCore.Mvc.ApplicationParts;
using Microsoft.AspNetCore.Mvc.Controllers;
using Xunit;

namespace Libplanet.Explorer.Tests.Controllers
{
    public class GenericControllerFeatureProviderTests
    {
        [Fact]
        public void ImplementsApplicationFeatureProvider()
        {
            var sut = new GenericControllerFeatureProvider<TestAction>();
            Assert.IsAssignableFrom<IApplicationFeatureProvider<ControllerFeature>>(sut);
        }

        [Fact]
        public void PopulateFeatureAddsExplorerControllerOfType()
        {
            var sut = new GenericControllerFeatureProvider<TestAction>();
            var feature = new ControllerFeature();
            sut.PopulateFeature(Enumerable.Empty<ApplicationPart>(), feature);
            Assert.Contains(typeof(ExplorerController<TestAction>), feature.Controllers);
        }

        [Fact]
        public void PopulateFeatureDoesntAddExistingActionController()
        {
            var sut = new GenericControllerFeatureProvider<TestAction>();
            var feature = new ControllerFeature();
            feature.Controllers.Add(typeof(TestActionController).GetTypeInfo());
            sut.PopulateFeature(Enumerable.Empty<ApplicationPart>(), feature);
            Assert.DoesNotContain(typeof(ExplorerController<TestAction>), feature.Controllers);
        }

        private class TestAction : IAction
        {
            public void LoadPlainValue(IValue plainValue)
            {
            }

            public IAccountStateDelta Execute(IActionContext context) => context.PreviousStates;

            public void Render(IActionContext context, IAccountStateDelta nextStates)
            {
            }

            public void RenderError(IActionContext context, Exception exception)
            {
            }

            public void Unrender(IActionContext context, IAccountStateDelta nextStates)
            {
            }

            public void UnrenderError(IActionContext context, Exception exception)
            {
            }

            public IValue PlainValue =>
                default(Dictionary);
        }

        private class TestActionController
        {
        }
    }
}
