using System.Linq;
using System.Reflection;
using Libplanet.Action;
using Libplanet.Explorer.Controllers;
using Microsoft.AspNetCore.Mvc.ApplicationParts;
using Microsoft.AspNetCore.Mvc.Controllers;
using Xunit;

namespace Libplanet.Explorer.UnitTests.Controllers
{
    public class GenericControllerFeatureProviderTests
    {
        [Fact]
        public void ImplementsApplicationFeatureProvider()
        {
            var sut = new GenericControllerFeatureProvider<NullAction>();
            Assert.IsAssignableFrom<IApplicationFeatureProvider<ControllerFeature>>(sut);
        }

        [Fact]
        public void PopulateFeatureAddsExplorerControllerOfType()
        {
            var sut = new GenericControllerFeatureProvider<NullAction>();
            var feature = new ControllerFeature();
            sut.PopulateFeature(Enumerable.Empty<ApplicationPart>(), feature);
            Assert.Contains(typeof(ExplorerController<NullAction>), feature.Controllers);
        }

        [Fact]
        public void PopulateFeatureDoesntAddExistingActionController()
        {
            var sut = new GenericControllerFeatureProvider<NullAction>();
            var feature = new ControllerFeature();
            feature.Controllers.Add(typeof(NullActionController).GetTypeInfo());
            sut.PopulateFeature(Enumerable.Empty<ApplicationPart>(), feature);
            Assert.DoesNotContain(typeof(ExplorerController<NullAction>), feature.Controllers);
        }

        private class NullActionController
        {
        }
    }
}
