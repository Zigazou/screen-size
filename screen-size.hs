module Main where
import Haste
import Haste.DOM
import Haste.Events
import Data.Maybe
import Numeric

data ScreenSizes = ScreenSizes { ssRatio :: Double
                               , ssDiagonal :: Double
                               , ssWidth :: Double
                               , ssHeight :: Double
                               }

data SSWidgets = SSWidgets { sswRatio :: Elem
                           , sswDiagonal :: Elem
                           , sswWidth :: Elem
                           , sswHeight :: Elem
                           , sswPreview :: Elem
                           , sswUnit :: Elem
                           }

data CalcType = CalcWidthHeight
              | CalcDiagonalWidth
              | CalcDiagonalHeight
              deriving (Eq)

firstElemQS :: MonadIO m => Elem -> QuerySelector -> m (Maybe Elem)
firstElemQS from selector = elemsByQS from selector >>= return . listToMaybe

getDefault :: (MonadIO m, JSType a) => a -> Elem -> m a
getDefault defValue element = getValue element >>= return . fromMaybe defValue

getOneSSW :: MonadIO m => Elem -> m (Maybe SSWidgets)
getOneSSW root = do
    ratio <- firstElemQS root ".js-ratio"
    diagonal <- firstElemQS root ".js-diagonal"
    width <- firstElemQS root ".js-width"
    height <- firstElemQS root ".js-height"
    preview <- firstElemQS root ".js-screen-preview"
    unit <- firstElemQS root ".js-screen-unit"

    return $ SSWidgets <$> ratio <*> diagonal <*> width <*> height <*> preview
                       <*> unit

getSSWidgets :: MonadIO m => m [SSWidgets]
getSSWidgets =
    elemsByClass "js-screen-size" >>= mapM getOneSSW >>= return . catMaybes

ratioValue :: String -> Double
ratioValue "5-4" = 5 / 4
ratioValue "4-3" = 4 / 3
ratioValue "16-10" = 16 / 10
ratioValue "16-9" = 16 / 9
ratioValue "21-9" = 21 / 9
ratioValue _   = 1

calc :: CalcType -> ScreenSizes -> ScreenSizes
calc CalcWidthHeight ss = ss { ssWidth = h * ssRatio ss, ssHeight = h }
    where h = sqrt (ssDiagonal ss * ssDiagonal ss
                   / (1 + ssRatio ss * ssRatio ss)
                   )

calc CalcDiagonalWidth ss = ss { ssDiagonal = diagonal, ssWidth = width }
    where width = ssHeight ss * ssRatio ss
          diagonal = sqrt (width * width + ssHeight ss * ssHeight ss)

calc CalcDiagonalHeight ss = ss { ssDiagonal = diagonal, ssHeight = height }
    where height = ssWidth ss * (1 / ssRatio ss)
          diagonal = sqrt (ssWidth ss * ssWidth ss + height * height)

getScreenSizes :: MonadIO m => SSWidgets -> m ScreenSizes
getScreenSizes ssw =
    ScreenSizes <$> (getDefault "" (sswRatio ssw) >>= return . ratioValue)
                <*> getDefault 0.0 (sswDiagonal ssw)
                <*> getDefault 0.0 (sswWidth ssw)
                <*> getDefault 0.0 (sswHeight ssw)

prettyDouble :: Double -> String
prettyDouble value | frac < 0.1 = toString int
                   | otherwise = showFFloat (Just 1) value ""
                   where (int, frac) = properFraction value :: (Integer, Double)

putScreenSizes :: MonadIO m => CalcType -> SSWidgets -> ScreenSizes -> m ()
putScreenSizes CalcWidthHeight ssw ss = do
    setProp (sswWidth ssw) "value" (prettyDouble $ ssWidth ss)
    setProp (sswHeight ssw) "value" (prettyDouble $ ssHeight ss)

putScreenSizes CalcDiagonalWidth ssw ss = do
    setProp (sswDiagonal ssw) "value" (prettyDouble $ ssDiagonal ss)
    setProp (sswWidth ssw) "value" (prettyDouble $ ssWidth ss)

putScreenSizes CalcDiagonalHeight ssw ss = do
    setProp (sswDiagonal ssw) "value" (prettyDouble $ ssDiagonal ss)
    setProp (sswHeight ssw) "value" (prettyDouble $ ssHeight ss)

recalculate :: MonadEvent m => SSWidgets -> CalcType -> m ()
recalculate ssw ct = getScreenSizes ssw >>= putScreenSizes ct ssw . calc ct

updatePreview :: MonadEvent m => SSWidgets -> m ()
updatePreview ssw = do
    ratio <- getDefault "16-9" (sswRatio ssw)
    let preview = sswPreview ssw
    mapQS_ preview "img" $ \e -> setClass e "screen-disabled" True
    mapQS_ preview (".js-" ++ ratio) $ \e -> setClass e "screen-disabled" False

updateUnit :: MonadEvent m => SSWidgets -> m ()
updateUnit ssw = do
    unit <- getDefault "" (sswUnit ssw)
    let converter = case unit of "in" -> 1 / 2.54
                                 "cm" -> 2.54
                                 _ -> 1
    diagonal <- getDefault 0.0 (sswDiagonal ssw)
    setProp (sswDiagonal ssw) "value" (prettyDouble $ diagonal * converter)

installHandlers :: MonadEvent m => SSWidgets -> m HandlerInfo
installHandlers ssw = do
    onEvent (sswRatio ssw) Change $ \_ -> do
        updatePreview ssw
        recalculate ssw CalcWidthHeight

    onEvent (sswUnit ssw) Change $ \_ -> do
        updateUnit ssw
        recalculate ssw CalcWidthHeight

    onEvent (sswDiagonal ssw) KeyUp $ \_ -> recalculate ssw CalcWidthHeight
    onEvent (sswWidth ssw) KeyUp $ \_ -> recalculate ssw CalcDiagonalHeight
    onEvent (sswHeight ssw) KeyUp $ \_ -> recalculate ssw CalcDiagonalWidth

main :: IO ()
main = getSSWidgets >>= mapM_ installHandlers
