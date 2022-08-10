#from nose.plugins.skip import SkipTest
#from nose.tools import assert_raises, nottest

#@SkipTest
from bibanalyzer import mark_book_fields


class TestBasic:

    def setUp(self):
        lit = """        Kornus K., Lehner M., Schroeder M. Geometric Inflight Calibration of the Stereoscopic CCD-Linescanner // MOMS-2P, ISPRS Com I Symp., Bangalore. 1998. Vol. XXXII-1. P. 148-155.
        Roeser, S. And Bastian, U., 1991. "PPM Star Catalogue". Astronomisches Rechen-1.stitut, Heidelberg. Spectrum Akademischer Verlag. Heidelberg.
        Высокоскоростной алгоритм сегментации изображений звездного неба, полученных от датчиков сканерного типа / Д.Ю. Пашенцев и др. // Цифровая обработка сигналов: научно-технический журнал. 2011. №3. С. 42-46."""
        refs = lit.split("\n")
        self.parts = []
        for i, ref in enumerate(refs):
            p = mark_book_fields(ref)
            if not p:
                continue
            self.parts.append(p)

    def tearDown(self):
        pass

    def test_splitter(self):
        for p in self.parts:
            assert(len(p)>3), len(p)
