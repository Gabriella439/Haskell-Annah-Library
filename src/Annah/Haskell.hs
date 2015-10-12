{-# LANGUAGE RankNTypes #-}

{-| This module provides conversion from @annah@'s Prelude to the equivalent
    Haskell types

    The Haskell backend uses these to convert @annah@-generated expressions to 
    executable Haskell programs
-}

module Annah.Haskell (
    -- * Conversions
    io'ToIO,
    boolToBool',
    prod0ToUnit,
    string'ToString,
    stringToString',

    -- * Types
    IO',
    Bool',
    Prod0,
    String'
    ) where

import Data.Char (chr, ord)

-- | @annah@ encoding of `IO`
type IO' a =
        forall io x
    .   x
    ->  ((String' -> io) -> io)
    ->  (String' -> io -> io)
    ->  (a -> io)
    ->  io

-- | Convert from @annah@ `IO'` to Haskell `IO`
io'ToIO :: IO' Prod0 -> IO ()
io'ToIO io' = io'
    ()
    (\k               -> do str <- getLine; k (stringToString' str))
    (\str io          -> do putStrLn (string'ToString str); io)
    (\prod0 -> return (prod0ToUnit prod0))

-- | @annah@ encoding of `Bool`
type Bool' = forall bool x . x -> bool -> bool -> bool

-- | Convert a Haskell `Bool` to an @annah@ `Bool'`
boolToBool' :: Bool -> Bool'
boolToBool' True  _  t f = t
boolToBool' False _  t f = f

-- | @annah@ encoding of @()@
type Prod0 = forall prod0 x . x -> prod0 -> prod0

-- | Convert an @annah@ `Prod0` to a Haskell @()@
prod0ToUnit :: Prod0 -> ()
prod0ToUnit k = k () ()

-- | @annah@ encoding of ASCII `String`s
type String' =
         forall string x
    .   x
    ->  string
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->  (string -> string)
    ->   string

-- | Convert from @annah@ `String'` to a Haskell `String`
string'ToString :: String' -> String
string'ToString str = str
    ()
    ""
    (chr 127:)
    (chr 126:)
    (chr 125:)
    (chr 124:)
    (chr 123:)
    (chr 122:)
    (chr 121:)
    (chr 120:)
    (chr 119:)
    (chr 118:)
    (chr 117:)
    (chr 116:)
    (chr 115:)
    (chr 114:)
    (chr 113:)
    (chr 112:)
    (chr 111:)
    (chr 110:)
    (chr 109:)
    (chr 108:)
    (chr 107:)
    (chr 106:)
    (chr 105:)
    (chr 104:)
    (chr 103:)
    (chr 102:)
    (chr 101:)
    (chr 100:)
    (chr  99:)
    (chr  98:)
    (chr  97:)
    (chr  96:)
    (chr  95:)
    (chr  94:)
    (chr  93:)
    (chr  92:)
    (chr  91:)
    (chr  90:)
    (chr  89:)
    (chr  88:)
    (chr  87:)
    (chr  86:)
    (chr  85:)
    (chr  84:)
    (chr  83:)
    (chr  82:)
    (chr  81:)
    (chr  80:)
    (chr  79:)
    (chr  78:)
    (chr  77:)
    (chr  76:)
    (chr  75:)
    (chr  74:)
    (chr  73:)
    (chr  72:)
    (chr  71:)
    (chr  70:)
    (chr  69:)
    (chr  68:)
    (chr  67:)
    (chr  66:)
    (chr  65:)
    (chr  64:)
    (chr  63:)
    (chr  62:)
    (chr  61:)
    (chr  60:)
    (chr  59:)
    (chr  58:)
    (chr  57:)
    (chr  56:)
    (chr  55:)
    (chr  54:)
    (chr  53:)
    (chr  52:)
    (chr  51:)
    (chr  50:)
    (chr  49:)
    (chr  48:)
    (chr  47:)
    (chr  46:)
    (chr  45:)
    (chr  44:)
    (chr  43:)
    (chr  42:)
    (chr  41:)
    (chr  40:)
    (chr  39:)
    (chr  38:)
    (chr  37:)
    (chr  36:)
    (chr  35:)
    (chr  34:)
    (chr  33:)
    (chr  32:)
    (chr  31:)
    (chr  30:)
    (chr  29:)
    (chr  28:)
    (chr  27:)
    (chr  26:)
    (chr  25:)
    (chr  24:)
    (chr  23:)
    (chr  22:)
    (chr  21:)
    (chr  20:)
    (chr  19:)
    (chr  18:)
    (chr  17:)
    (chr  16:)
    (chr  15:)
    (chr  14:)
    (chr  13:)
    (chr  12:)
    (chr  11:)
    (chr  10:)
    (chr   9:)
    (chr   8:)
    (chr   7:)
    (chr   6:)
    (chr   5:)
    (chr   4:)
    (chr   3:)
    (chr   2:)
    (chr   1:)
    (chr   0:)

-- | Convert from a Haskell `String` to an @annah@ `String'`
stringToString' :: String -> String'
stringToString' str =
    \_
    nil
    cons127
    cons126
    cons125
    cons124
    cons123
    cons122
    cons121
    cons120
    cons119
    cons118
    cons117
    cons116
    cons115
    cons114
    cons113
    cons112
    cons111
    cons110
    cons109
    cons108
    cons107
    cons106
    cons105
    cons104
    cons103
    cons102
    cons101
    cons100
    cons099
    cons098
    cons097
    cons096
    cons095
    cons094
    cons093
    cons092
    cons091
    cons090
    cons089
    cons088
    cons087
    cons086
    cons085
    cons084
    cons083
    cons082
    cons081
    cons080
    cons079
    cons078
    cons077
    cons076
    cons075
    cons074
    cons073
    cons072
    cons071
    cons070
    cons069
    cons068
    cons067
    cons066
    cons065
    cons064
    cons063
    cons062
    cons061
    cons060
    cons059
    cons058
    cons057
    cons056
    cons055
    cons054
    cons053
    cons052
    cons051
    cons050
    cons049
    cons048
    cons047
    cons046
    cons045
    cons044
    cons043
    cons042
    cons041
    cons040
    cons039
    cons038
    cons037
    cons036
    cons035
    cons034
    cons033
    cons032
    cons031
    cons030
    cons029
    cons028
    cons027
    cons026
    cons025
    cons024
    cons023
    cons022
    cons021
    cons020
    cons019
    cons018
    cons017
    cons016
    cons015
    cons014
    cons013
    cons012
    cons011
    cons010
    cons009
    cons008
    cons007
    cons006
    cons005
    cons004
    cons003
    cons002
    cons001
    cons000 ->
    let cons c = case ord c of
            0   -> cons000
            1   -> cons001
            2   -> cons002
            3   -> cons003
            4   -> cons004
            5   -> cons005
            6   -> cons006
            7   -> cons007
            8   -> cons008
            9   -> cons009
            10  -> cons010
            11  -> cons011
            12  -> cons012
            13  -> cons013
            14  -> cons014
            15  -> cons015
            16  -> cons016
            17  -> cons017
            18  -> cons018
            19  -> cons019
            20  -> cons020
            21  -> cons021
            22  -> cons022
            23  -> cons023
            24  -> cons024
            25  -> cons025
            26  -> cons026
            27  -> cons027
            28  -> cons028
            29  -> cons029
            30  -> cons030
            31  -> cons031
            32  -> cons032
            33  -> cons033
            34  -> cons034
            35  -> cons035
            36  -> cons036
            37  -> cons037
            38  -> cons038
            39  -> cons039
            40  -> cons040
            41  -> cons041
            42  -> cons042
            43  -> cons043
            44  -> cons044
            45  -> cons045
            46  -> cons046
            47  -> cons047
            48  -> cons048
            49  -> cons049
            50  -> cons050
            51  -> cons051
            52  -> cons052
            53  -> cons053
            54  -> cons054
            55  -> cons055
            56  -> cons056
            57  -> cons057
            58  -> cons058
            59  -> cons059
            60  -> cons060
            61  -> cons061
            62  -> cons062
            63  -> cons063
            64  -> cons064
            65  -> cons065
            66  -> cons066
            67  -> cons067
            68  -> cons068
            69  -> cons069
            70  -> cons070
            71  -> cons071
            72  -> cons072
            73  -> cons073
            74  -> cons074
            75  -> cons075
            76  -> cons076
            77  -> cons077
            78  -> cons078
            79  -> cons079
            80  -> cons080
            81  -> cons081
            82  -> cons082
            83  -> cons083
            84  -> cons084
            85  -> cons085
            86  -> cons086
            87  -> cons087
            88  -> cons088
            89  -> cons089
            90  -> cons090
            91  -> cons091
            92  -> cons092
            93  -> cons093
            94  -> cons094
            95  -> cons095
            96  -> cons096
            97  -> cons097
            98  -> cons098
            99  -> cons099
            100 -> cons100
            101 -> cons101
            102 -> cons102
            103 -> cons103
            104 -> cons104
            105 -> cons105
            106 -> cons106
            107 -> cons107
            108 -> cons108
            109 -> cons109
            110 -> cons110
            111 -> cons111
            112 -> cons112
            113 -> cons113
            114 -> cons114
            115 -> cons115
            116 -> cons116
            117 -> cons117
            118 -> cons118
            119 -> cons119
            120 -> cons120
            121 -> cons121
            122 -> cons122
            123 -> cons123
            124 -> cons124
            125 -> cons125
            126 -> cons126
            127 -> cons127
            _   -> error ("stringToString' - Invalid ASCII character: " ++ [c])
    in  foldr cons nil str
