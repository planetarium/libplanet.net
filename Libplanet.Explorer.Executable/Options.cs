using System;
using System.Collections.Generic;
using System.Linq;
using System.Net;
using Libplanet.Action;
using Libplanet.Blocks;
using Libplanet.Crypto;
using Libplanet.Net;

namespace Libplanet.Explorer.Executable
{
    public class Options
    {
        public Options(
            bool debug,
            string host,
            int port,
            int blockIntervalMilliseconds,
            long minimumDifficulty,
            int difficultyBoundDivisor,
            int workers,
            string appProtocolVersionToken,
            string mysqlServer,
            uint? mysqlPort,
            string mysqlUsername,
            string mysqlPassword,
            string mysqlDatabase,
            int maxTransactionsPerBlock,
            int maxBlockBytes,
            int maxGenesisBytes,
            IEnumerable<string> seedStrings,
            string iceServerUrl,
            string storePath,
            string storeType,
            string genesisBlockPath
        )
        {
            Debug = debug;
            Host = host;
            Port = port;
            BlockIntervalMilliseconds = blockIntervalMilliseconds;
            MinimumDifficulty = minimumDifficulty;
            DifficultyBoundDivisor = difficultyBoundDivisor;
            Workers = workers;
            AppProtocolVersionToken = appProtocolVersionToken;
            MySQLServer = mysqlServer;
            MySQLPort = mysqlPort;
            MySQLUsername = mysqlUsername;
            MySQLPassword = mysqlPassword;
            MySQLDatabase = mysqlDatabase;
            MaxTransactionsPerBlock = maxTransactionsPerBlock;
            MaxBlockBytes = maxBlockBytes;
            MaxGenesisBytes = maxGenesisBytes;
            SeedStrings = seedStrings;
            IceServerUrl = iceServerUrl;
            StorePath = storePath;
            StoreType = storeType;
            GenesisBlockPath = genesisBlockPath;
        }

        public bool Debug { get; set; }

        public string Host { get; set; }

        public int Port { get; set; }

        public int BlockIntervalMilliseconds { get; set; }

        public long MinimumDifficulty { get; set; }

        public int DifficultyBoundDivisor { get; set; }

        public int Workers { get; set; }

        public string AppProtocolVersionToken { get; set; }

        public string MySQLServer { get; set; }

        public uint? MySQLPort { get; set; }

        public string MySQLUsername { get; set; }

        public string MySQLPassword { get; set; }

        public string MySQLDatabase { get; set; }

        public int MaxTransactionsPerBlock { get; set; }

        public int MaxBlockBytes { get; set; }

        public int MaxGenesisBytes { get; set; }

        public IEnumerable<string> SeedStrings
        {
            get
            {
                return Seeds?.Select(seed => $"{ByteUtil.Hex(seed.PublicKey.Format(true))}," +
                                             $"{seed.EndPoint.Host},{seed.EndPoint.Port}");
            }

            set
            {
                Seeds = value?.Select(str =>
                {
                    string[] parts = str.Split(',');
                    if (parts.Length != 3)
                    {
                        throw new FormatException(
                            $"A seed must be a command-separated triple. {str}");
                    }

                    byte[] pubkeyBytes = ByteUtil.ParseHex(parts[0]);
                    var pubkey = new PublicKey(pubkeyBytes);
                    var endpoint = new DnsEndPoint(parts[1], int.Parse(parts[2]));
                    return new BoundPeer(pubkey, endpoint);
                });
            }
        }

        public IEnumerable<BoundPeer> Seeds { get; set; }

        public string IceServerUrl
        {
            get
            {
                if (IceServer is null)
                {
                    return null;
                }

                Uri uri = IceServer.Urls.First();
                var uriBuilder = new UriBuilder(uri)
                {
                    UserName = IceServer.Username,
                    Password = IceServer.Credential,
                };
                return uriBuilder.Uri.ToString();
            }

            set
            {
                if (value is null)
                {
                    IceServer = null;
                    return;
                }

                var uri = new Uri(value);
                string[] userInfo = uri.UserInfo.Split(':', count: 2);
                IceServer = new IceServer(new[] { uri }, userInfo[0], userInfo[1]);
            }
        }

        public IceServer IceServer { get; set; }

        public string StorePath { get; set; }

        public string StoreType { get; set; }

        public string GenesisBlockPath { get; set; }

        internal Block<NullAction> GenesisBlock
        {
            get
            {
                var uri = new Uri(GenesisBlockPath);
                using (var client = new WebClient())
                {
                    var serialized = client.DownloadData(uri);
                    return Block<NullAction>.Deserialize(serialized);
                }
            }
        }
    }
}
