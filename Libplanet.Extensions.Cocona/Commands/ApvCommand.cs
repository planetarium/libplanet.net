using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Threading.Tasks;
using Bencodex;
using Bencodex.Types;
using global::Cocona;
using Libplanet.Crypto;
using Libplanet.KeyStore;
using Libplanet.Net;
using Libplanet.Net.Transports;

namespace Libplanet.Extensions.Cocona.Commands
{
    public class ApvCommand
    {
        [Command(Description = "Sign a new app protocol version.")]
        public void Sign(
            [Argument(Name = "KEY-ID", Description = "A private key to use for signing.")]
            Guid keyId,
            [Argument(Name = "VERSION", Description = "A version number to sign.")]
            int version,
            [Option(
                'p',
                ValueName = "PASSPHRASE",
                Description = "Take passphrase through this option instead of prompt."
            )]
            string? passphrase = null,
            [Option(
                'E',
                ValueName = "FILE",
                Description = "Bencodex file to use for extra data.  " +
                    "For standard input, use a hyphen (`-').  " +
                    "For an actual file named a hyphen, prepend `./', i.e., `./-'."
            )]
            string? extraFile = null,
            [Option(
                'e',
                ValueName = "KEY=VALUE",
                Description = "Set a value to a key on extra Bencodex dictionary.  " +
                    "Can be applied multiple times (e.g., `-e foo=1 -e bar=baz').  " +
                    "This option implies the extra data to be a Bencodex dictionary, " +
                    "hence cannot be used together with -E/--extra-file option."
            )]
            string[]? extra = null
        )
        {
            PrivateKey key = new KeyCommand().UnprotectKey(keyId, passphrase);
            IValue? extraValue = null;
            if (extraFile is string path)
            {
                if (extra is string[] e && e.Length > 0)
                {
                    throw Utils.Error(
                        "-E/--extra-file and -e/--extra cannot be used together at a time."
                    );
                }

                var codec = new Codec();
                if (path == "-")
                {
                    // Stream for stdin does not support .Seek()
                    using MemoryStream buffer = new MemoryStream();
                    using (Stream stream = Console.OpenStandardInput())
                    {
                        stream.CopyTo(buffer);
                    }

                    buffer.Seek(0, SeekOrigin.Begin);
                    extraValue = codec.Decode(buffer);
                }
                else
                {
                    using Stream stream = File.Open(path, FileMode.Open, FileAccess.Read);
                    extraValue = codec.Decode(stream);
                }
            }
            else if (extra is string[] e && e.Length > 0)
            {
                var dict = Bencodex.Types.Dictionary.Empty;
                foreach (string pair in e)
                {
                    int sepPos = pair.IndexOf('=');
                    if (sepPos < 0)
                    {
                        throw Utils.Error(
                            "-e/--extra must be a pair of KEY=VALUE, but no equal (=) separator: " +
                            $"`{pair}'."
                        );
                    }

                    string key_ = pair.Substring(0, sepPos);
                    string value = pair.Substring(sepPos + 1);
                    dict = dict.SetItem(key_, value);
                }

                extraValue = dict;
            }

            AppProtocolVersion v = AppProtocolVersion.Sign(key, version, extraValue);
            Console.WriteLine(v.Token);
        }

        [Command(Description = "Verify a given app protocol version token's signature.")]
        public void Verify(
            [Argument(
                Name = "APV-TOKEN",
                Description = "An app protocol version token to verify.  " +
                    "Read from the standard input if omitted."
            )]
            string? token = null,
            [Option(
                'p',
                ValueName = "PUBLIC-KEY",
                Description = "Public key(s) to be used for verification.  " +
                    "Can be applied multiple times."
            )]
            string[]? publicKey = null,
            [Option(
                'K',
                Description = "Do not use any keys in the key store, " +
                    "but only -p/--public-key options."
            )]
            bool noKeyStore = false
        )
        {
            AppProtocolVersion v = ParseAppProtocolVersionToken(token);

            if (publicKey is string[] pubKeyHexes)
            {
                foreach (string pubKeyHex in pubKeyHexes)
                {
                    string opt = $"-p/--public-key=\"{pubKeyHex}\"";
                    PublicKey pubKey;
                    try
                    {
                        pubKey = new PublicKey(ByteUtil.ParseHex(pubKeyHex));
                    }
                    catch (Exception e)
                    {
                        throw Utils.Error($"The {opt} is not a valid public key.  {e.Message}");
                    }

                    if (v.Verify(pubKey))
                    {
                        Console.Error.WriteLine(
                            "The signature successfully was verified using the {0}.",
                            opt
                        );
                        return;
                    }

                    Console.Error.WriteLine(
                        "The signature was failed to verify using the {0}.",
                        opt
                    );
                }
            }

            if (!noKeyStore)
            {
                KeyCommand keyInstance = new KeyCommand();
                IEnumerable<Tuple<Guid, ProtectedPrivateKey>> ppks = keyInstance.KeyStore.List()
                    .Where(pair => pair.Item2.Address.Equals(v.Signer));
                foreach (Tuple<Guid, ProtectedPrivateKey> pair in ppks)
                {
                    pair.Deconstruct(out Guid keyId, out ProtectedPrivateKey ppk);
                    PublicKey pubKey = keyInstance.UnprotectKey(keyId).PublicKey;
                    if (v.Verify(pubKey))
                    {
                        Console.Error.WriteLine(
                            "The signature successfully was verified using the key {0}.",
                            keyId
                        );
                        return;
                    }

                    Console.Error.WriteLine(
                        "The signature was failed to verify using the key {0}.",
                        keyId
                    );
                }
            }

            throw Utils.Error("Failed to verify.");
        }

        [Command(Description = "Parse and analyze a given app protocol version token.")]
        public void Analyze(
            [Argument(
                Name = "APV-TOKEN",
                Description = "An app protocol version token to analyze.  " +
                    "Read from the standard input if omitted."
            )]
            string? token = null,
            [Option(Description = "Print information of given token as JSON.")]
            bool json = false
        )
        {
            AppProtocolVersion v = ParseAppProtocolVersionToken(token);

            var data = new List<(string, string)>
            {
                ("version", v.Version.ToString(CultureInfo.InvariantCulture)),
                ("signature", ByteUtil.Hex(v.Signature)),
                ("signer", v.Signer.ToString()),
            };

            if (v.Extra is IValue extra)
            {
                void TreeIntoTable(IValue tree, List<(string, string)> table, string key)
                {
                    switch (tree)
                    {
                        case Null _:
                            table.Add((key, "null"));
                            return;

                        case Bencodex.Types.Boolean b:
                            table.Add((key, b ? "true" : "false"));
                            return;

                        case Binary bin:
                            table.Add((key, ByteUtil.Hex(bin.ToByteArray())));
                            return;

                        case Text t:
                            table.Add((key, t.Value));
                            return;

                        case Bencodex.Types.Integer i:
                            table.Add((key, i.Value.ToString(CultureInfo.InvariantCulture)));
                            return;

                        case Bencodex.Types.List l:
                            int idx = 0;
                            foreach (IValue el in l)
                            {
                                TreeIntoTable(el, table, $"{key}[{idx}]");
                                idx++;
                            }

                            return;

                        case Bencodex.Types.Dictionary d:
                            foreach (KeyValuePair<IKey, IValue> kv in d)
                            {
                                string k = kv.Key switch
                                {
                                    Binary bk => ByteUtil.Hex(bk),
                                    Text txt => txt.Value,
                                    _ => kv.Key.ToString() ?? string.Empty,
                                };
                                TreeIntoTable(kv.Value, table, $"{key}.{k}");
                            }

                            return;

                        default:
                            table.Add((key, tree.ToString() ?? string.Empty));
                            return;
                    }
                }

                TreeIntoTable(v.Extra, data, "extra");
            }

            if (json)
            {
                Console.WriteLine(
                    JsonSerializer.Serialize(
                        data.ToDictionary(e => e.Item1, e => e.Item2)));
            }
            else
            {
                Utils.PrintTable(("Field", "Value"), data);
            }
        }

        [Command(Description = "Query app protocol version (a.k.a. APV) of target node.")]
        public async Task Query(
            [Argument(
                Name = "TARGET",
#pragma warning disable MEN002 // Line is too long
                Description = "Comma seperated peer information({pubkey},{host},{port}) of target node. (e.g. 027bd36895d68681290e570692ad3736750ceaab37be402442ffb203967f98f7b6,9c.planetarium.dev,31236)")]
#pragma warning restore MEN002 // Line is too long
            string peerInfo)
        {
            BoundPeer peer;
            AppProtocolVersion apv;

            try
            {
                peer = BoundPeer.ParsePeer(peerInfo);
            }
            catch
            {
                throw Utils.Error($"Failed to parse peer. Please check the input. [{peerInfo}]");
            }

            try
            {
                apv = await peer.QueryAppProtocolVersionTcp();
            }
            catch
            {
                throw Utils.Error($"Failed to query app protocol version.");
            }

            Console.WriteLine(apv.Token);
        }

        private AppProtocolVersion ParseAppProtocolVersionToken(string? token)
        {
            if (token is null)
            {
                token = Console.ReadLine();
            }

            try
            {
                return AppProtocolVersion.FromToken(token.Trim());
            }
            catch (FormatException e)
            {
                throw Utils.Error($"Not a valid app protocol version token.  {e.Message}");
            }
        }
    }
}
