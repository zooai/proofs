import type { Metadata } from 'next'
import { Zen, ZenMono } from '@hanzo/font'
import { ThemeProvider } from 'next-themes'
import { siteConfig } from '@/config/proofs'
import './global.css'

const sans = Zen

const mono = ZenMono

export const metadata: Metadata = {
  title: `${siteConfig.name} Formal Proofs`,
  description: siteConfig.description,
  openGraph: {
    title: `${siteConfig.name} Formal Proofs`,
    description: siteConfig.description,
    url: 'https://proofs.zoo.ngo',
    siteName: `${siteConfig.name} Proofs`,
    type: 'website',
  },
  twitter: {
    card: 'summary_large_image',
    title: `${siteConfig.name} Formal Proofs`,
    description: siteConfig.description,
  },
}

export default function RootLayout({
  children,
}: {
  children: React.ReactNode
}) {
  return (
    <html
      lang="en"
      className={`${sans.variable} ${mono.variable}`}
      suppressHydrationWarning
    >
      <head>
        <script
          dangerouslySetInnerHTML={{
            __html: `(function(){try{var d=document.documentElement;var s=localStorage.getItem('zoo-proofs-theme');if(s==='dark'||(s!=='light'&&window.matchMedia('(prefers-color-scheme:dark)').matches)){d.classList.add('dark')}else{d.classList.remove('dark')}}catch(e){}})()`,
          }}
        />
      </head>
      <body className="min-h-svh bg-background font-sans antialiased">
        <ThemeProvider
          attribute="class"
          defaultTheme="dark"
          storageKey="zoo-proofs-theme"
          enableSystem
        >
          {children}
        </ThemeProvider>
      </body>
    </html>
  )
}
